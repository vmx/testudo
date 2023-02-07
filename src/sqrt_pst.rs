use crate::mipp::MippProof;
use ark_bls12_377::{Bls12_377 as I, G1Affine, G2Affine};
use ark_ec::{msm::VariableBaseMSM, PairingEngine, ProjectiveCurve};
use ark_ff::{BigInteger256, One, PrimeField};
use ark_poly_commit::multilinear_pc::{
  data_structures::{Commitment, CommitterKey, Proof, VerifierKey},
  MultilinearPC,
};
use ark_serialize::CanonicalSerialize;
use rayon::prelude::{
  IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, ParallelIterator,
};

use super::scalar::Scalar;
use crate::{
  dense_mlpoly::DensePolynomial,
  math::Math,
  poseidon_transcript::{AppendToPoseidon, PoseidonTranscript},
  timer::Timer,
  transcript,
};

pub struct Polynomial {
  m: usize,
  polys: Vec<DensePolynomial>,
  q: Option<DensePolynomial>,
  chis_b: Option<Vec<Scalar>>,
}

impl Polynomial {
  // Given the evaluations over the boolean hypercube of a polynomial p of size
  // 2*m compute the sqrt-sized polynomials p_i as
  // p_i(Y) = \sum_{j \in \{0,1\}^m} p(j, i) * chi_j(Y)
  // where p(X,Y) = \sum_{i \in \{0,\1}^m} chi_i(X) * p_i(Y)
  //
  // TODO: add case when the length of the list is not an even power of 2
  pub fn from_evaluations(Z: &[Scalar]) -> Self {
    let pl_timer = Timer::new("poly_list_build");
    // check the evaluation list is a power of 2
    debug_assert!(Z.len() & (Z.len() - 1) == 0);
    let m = Z.len().log_2() / 2;
    let pow_m = 2_usize.pow(m as u32);
    let polys: Vec<DensePolynomial> = (0..pow_m)
      .into_par_iter()
      .map(|i| {
        let z: Vec<Scalar> = (0..pow_m)
          .into_par_iter()
          .map(|j| Z[(j << m) | i])
          .collect();
        DensePolynomial::new(z)
      })
      .collect();
    debug_assert!(polys.len() == pow_m);
    pl_timer.stop();
    Self {
      m,
      polys,
      q: None,
      chis_b: None,
    }
  }

  // Given point = (\vec{a}, \vec{b}), compute the polynomial q as
  // q(Y) =
  // \sum_{j \in \{0,1\}^m}(\sum_{i \in \{0,1\}^m} p(j,i) * chi_i(b)) * chi_j(Y)
  // and p(a,b) = q(b) where p is the initial polynomial
  fn get_q(&mut self, point: &[Scalar]) {
    let q_timer = Timer::new("build_q");
    debug_assert!(point.len() == 2 * self.m);
    let a = &point[0..self.m];
    let b = &point[self.m..2 * self.m];
    let pow_m = 2_usize.pow(self.m as u32);

    let chis: Vec<Scalar> = (0..pow_m)
      .into_par_iter()
      .map(|i| Self::get_chi_i(b, i))
      .collect();

    let z_q: Vec<Scalar> = (0..pow_m)
      .into_par_iter()
      .map(|j| (0..pow_m).map(|i| self.polys[i].Z[j] * chis[i]).sum())
      .collect();
    q_timer.stop();

    self.q = Some(DensePolynomial::new(z_q));
    self.chis_b = Some(chis);
  }

  // Given point = (\vec{a}, \vec{b}) used to construct q
  // compute q(b) = p(a,b).
  pub fn eval(&mut self, point: &[Scalar]) -> Scalar {
    let a = &point[0..point.len() / 2];
    let b = &point[point.len() / 2..point.len()];
    if self.q.is_none() {
      self.get_q(point);
    }
    let q = self.q.clone().unwrap();
    let prods = (0..q.Z.len())
      .into_par_iter()
      .map(|j| q.Z[j] * Polynomial::get_chi_i(&a, j));

    prods.sum()
  }

  pub fn commit(&self, ck: &CommitterKey<I>) -> (Vec<Commitment<I>>, <I as PairingEngine>::Fqk) {
    let timer_commit = Timer::new("sqrt_commit");

    let timer_list = Timer::new("comm_list");

    // commit to each of the sqrt sized p_i
    let comm_list: Vec<Commitment<I>> = self
      .polys
      .par_iter()
      .map(|p| MultilinearPC::<I>::commit(&ck, p))
      .collect();
    timer_list.stop();

    let h_vec = ck.powers_of_h[0].clone();
    assert!(comm_list.len() == h_vec.len());

    let ipp_timer = Timer::new("ipp");
    let pairings: Vec<_> = comm_list
      .clone()
      .into_par_iter()
      .map(|c| <I as PairingEngine>::G1Prepared::from(c.g_product))
      .zip(
        h_vec
          .into_par_iter()
          .map(|h| <I as PairingEngine>::G2Prepared::from(h)),
      )
      .collect();

    // compute the IPP commitment
    let t = I::product_of_pairings(pairings.iter());
    ipp_timer.stop();

    timer_commit.stop();

    (comm_list, t)
  }

  pub fn get_chi_i(b: &[Scalar], i: usize) -> Scalar {
    let m = b.len();
    let mut prod = Scalar::one();
    for j in 0..m {
      let b_j = b[j];
      if i >> (m - j - 1) & 1 == 1 {
        prod = prod * b_j;
      } else {
        prod = prod * (Scalar::one() - b_j)
      };
    }
    prod
  }

  pub fn open(
    &mut self,
    transcript: &mut PoseidonTranscript,
    comm_list: Vec<Commitment<I>>,
    ck: &CommitterKey<I>,
    point: &[Scalar],
    t: &<I as PairingEngine>::Fqk,
  ) -> (Commitment<I>, Proof<I>, MippProof<I>) {
    let m = point.len() / 2;
    let a = &point[0..m];

    if self.q.is_none() {
      self.get_q(point);
    }

    let q = self.q.clone().unwrap();

    if self.q.is_none() {
      self.get_q(point);
    }

    let q = self.q.clone().unwrap();

    let timer_open = Timer::new("sqrt_open");

    // Compute the PST commitment to q obtained as the inner products of the
    // commitments to the polynomials p_i and chi_i(a) for i ranging over the
    // boolean hypercube of size m.
    let m = a.len();
    let timer_msm = Timer::new("msm");
    if self.chis_b.is_none() {
      panic!("chis(b) should have been computed for q");
    }
    let chis = self.chis_b.clone().unwrap();
    let chis_repr: Vec<BigInteger256> = chis.par_iter().map(|y| y.into_repr()).collect();
    assert!(chis_repr.len() == comm_list.len());

    let a_vec: Vec<_> = comm_list.par_iter().map(|c| c.g_product).collect();

    let c_u =
      VariableBaseMSM::multi_scalar_mul(a_vec.as_slice(), chis_repr.as_slice()).into_affine();
    timer_msm.stop();

    let U: Commitment<I> = Commitment {
      nv: q.num_vars,
      g_product: c_u,
    };
    let comm = MultilinearPC::<I>::commit(ck, &q);
    debug_assert!(c_u == comm.g_product);
    let h_vec = ck.powers_of_h[0].clone();

    // MIPP proof that U is the inner product of the vector A
    //  and the vector y, where A is the opening vector to T
    let timer_mipp_proof = Timer::new("mipp_prove");
    let mipp_proof =
      MippProof::<I>::prove::<PoseidonTranscript>(transcript, ck, a_vec, chis, h_vec, &c_u, t)
        .unwrap();
    timer_mipp_proof.stop();

    // PST proof for opening q at a
    let timer_proof = Timer::new("pst_open");
    let mut a_rev = a.to_vec().clone();
    a_rev.reverse();
    let pst_proof = MultilinearPC::<I>::open(ck, &q, &a_rev);
    timer_proof.stop();

    timer_open.stop();
    (U, pst_proof, mipp_proof)
  }

  pub fn verify(
    transcript: &mut PoseidonTranscript,
    vk: &VerifierKey<I>,
    U: &Commitment<I>,
    point: &[Scalar],
    v: Scalar,
    pst_proof: &Proof<I>,
    mipp_proof: &MippProof<I>,
    T: &<I as PairingEngine>::Fqk,
  ) -> bool {
    let len = point.len();
    let a = &point[0..len / 2];
    let b = &point[len / 2..len];
    let timer_mipp_verify = Timer::new("mipp_verify");
    let res_mipp = MippProof::<I>::verify::<PoseidonTranscript>(
      vk,
      transcript,
      mipp_proof,
      b.to_vec(),
      &U.g_product,
      T,
    );
    assert!(res_mipp == true);
    timer_mipp_verify.stop();

    let mut a_rev = a.to_vec().clone();
    a_rev.reverse();
    let timer_pst_verify = Timer::new("pst_verify");
    let res = MultilinearPC::<I>::check(vk, U, &a_rev, v, pst_proof);
    timer_pst_verify.stop();
    res
  }
}

#[cfg(test)]
mod tests {
  use std::clone;

  use crate::parameters::poseidon_params;

  use super::*;
  use ark_ff::Zero;
  use ark_std::UniformRand;
  #[test]
  fn check_sqrt_poly_eval() {
    let mut rng = ark_std::test_rng();
    let num_vars = 8;
    let len = 2_usize.pow(num_vars);
    let Z: Vec<Scalar> = (0..len)
      .into_iter()
      .map(|_| Scalar::rand(&mut rng))
      .collect();
    let r: Vec<Scalar> = (0..num_vars)
      .into_iter()
      .map(|_| Scalar::rand(&mut rng))
      .collect();

    let p = DensePolynomial::new(Z.clone());
    let res1 = p.evaluate(&r);

    let mut pl = Polynomial::from_evaluations(&Z.clone());
    let res2 = pl.eval(&r);

    assert!(res1 == res2);
  }

  #[test]
  fn check_new_poly_commit() {
    let mut rng = ark_std::test_rng();
    let num_vars = 4;
    let len = 2_usize.pow(num_vars);
    let Z: Vec<Scalar> = (0..len)
      .into_iter()
      .map(|_| Scalar::rand(&mut rng))
      .collect();
    let r: Vec<Scalar> = (0..num_vars)
      .into_iter()
      .map(|_| Scalar::rand(&mut rng))
      .collect();

    let gens = MultilinearPC::<I>::setup(2, &mut rng);
    let (ck, vk) = MultilinearPC::<I>::trim(&gens, 2);

    let mut pl = Polynomial::from_evaluations(&Z.clone());

    let v = pl.eval(&r);

    let (comm_list, t) = pl.commit(&ck);

    let params = poseidon_params();
    let mut prover_transcript = PoseidonTranscript::new(&params);

    let (u, pst_proof, mipp_proof) = pl.open(&mut prover_transcript, comm_list, &ck, &r, &t);

    let mut verifier_transcript = PoseidonTranscript::new(&params);

    let res = Polynomial::verify(
      &mut verifier_transcript,
      &vk,
      &u,
      &r,
      v,
      &pst_proof,
      &mipp_proof,
      &t,
    );
    assert!(res == true);
  }
}
