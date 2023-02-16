use crate::mipp::MippProof;
use ark_ec::{pairing::Pairing, scalar_mul::variable_base::VariableBaseMSM, CurveGroup};
use ark_ff::One;
use ark_poly_commit::multilinear_pc::{
  data_structures::{Commitment, CommitterKey, Proof, VerifierKey},
  MultilinearPC,
};
use rayon::prelude::{IntoParallelIterator, IntoParallelRefIterator, ParallelIterator};

use crate::{
  dense_mlpoly::DensePolynomial, math::Math, poseidon_transcript::PoseidonTranscript, timer::Timer,
};

pub struct Polynomial<E: Pairing> {
  m: usize,
  pub polys: Vec<DensePolynomial<E::ScalarField>>,
  q: Option<DensePolynomial<E::ScalarField>>,
  chis_b: Option<Vec<E::ScalarField>>,
}

impl<E: Pairing> Polynomial<E> {
  // Given the evaluations over the boolean hypercube of a polynomial p of size
  // 2*m compute the sqrt-sized polynomials p_i as
  // p_i(X) = \sum_{j \in \{0,1\}^m} p(j, i) * chi_j(X)
  // where p(X,Y) = \sum_{i \in \{0,\1}^m}
  //  (\sum_{j \in \{0, 1\}^{m}} p(j, i) * \chi_j(X)) * \chi_i(Y)
  // TODO: add case when the length of the list is not an even power of 2
  pub fn from_evaluations(Z: &[E::ScalarField]) -> Self {
    let pl_timer = Timer::new("poly_list_build");
    // check the evaluation list is a power of 2
    debug_assert!(Z.len() & (Z.len() - 1) == 0);
    let m = Z.len().log_2() / 2;
    let pow_m = 2_usize.pow(m as u32);
    let polys: Vec<DensePolynomial<E::ScalarField>> = (0..pow_m)
      .into_par_iter()
      .map(|i| {
        let z: Vec<E::ScalarField> = (0..pow_m)
          .into_par_iter()
          // viewing the list of evaluation as a square matrix
          // we select by row j and column i
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
  fn get_q(&mut self, point: &[E::ScalarField]) {
    let q_timer = Timer::new("build_q");
    debug_assert!(point.len() == 2 * self.m);
    let _a = &point[0..self.m];
    let b = &point[self.m..2 * self.m];
    let pow_m = 2_usize.pow(self.m as u32);

    let chis: Vec<E::ScalarField> = (0..pow_m)
      .into_par_iter()
      .map(|i| Self::get_chi_i(b, i))
      .collect();

    let z_q: Vec<E::ScalarField> = (0..pow_m)
      .into_par_iter()
      .map(|j| (0..pow_m).map(|i| self.polys[i].Z[j] * chis[i]).sum())
      .collect();
    q_timer.stop();

    self.q = Some(DensePolynomial::new(z_q));
    self.chis_b = Some(chis);
  }

  // Given point = (\vec{a}, \vec{b}) used to construct q
  // compute q(b) = p(a,b).
  pub fn eval(&mut self, point: &[E::ScalarField]) -> E::ScalarField {
    let a = &point[0..point.len() / 2];
    let _b = &point[point.len() / 2..point.len()];
    if self.q.is_none() {
      self.get_q(point);
    }
    let q = self.q.clone().unwrap();
    (0..q.Z.len())
      .into_par_iter()
      .map(|j| q.Z[j] * Polynomial::<E>::get_chi_i(&a, j))
      .sum()
  }

  pub fn commit(&self, ck: &CommitterKey<E>) -> (Vec<Commitment<E>>, E::TargetField) {
    let timer_commit = Timer::new("sqrt_commit");

    let timer_list = Timer::new("comm_list");

    // commit to each of the sqrt sized p_i
    let comm_list: Vec<Commitment<E>> = self
      .polys
      .par_iter()
      .map(|p| MultilinearPC::<E>::commit(&ck, p))
      .collect();
    timer_list.stop();

    let h_vec = ck.powers_of_h[0].clone();
    assert!(comm_list.len() == h_vec.len());

    let ipp_timer = Timer::new("ipp");
    let left_pairs: Vec<_> = comm_list
      .clone()
      .into_par_iter()
      .map(|c| E::G1Prepared::from(c.g_product))
      .collect();
    let right_pairs: Vec<_> = h_vec
      .into_par_iter()
      .map(|h| E::G2Prepared::from(h))
      .collect();

    // compute the IPP commitment
    let t = E::multi_pairing(left_pairs, right_pairs).0;
    ipp_timer.stop();

    timer_commit.stop();

    (comm_list, t)
  }

  // computes \chi_i(\vec{b}) = \prod_{i_j = 0}(1 - b_j)\prod_{i_j = 1}(b_j)
  pub fn get_chi_i(b: &[E::ScalarField], i: usize) -> E::ScalarField {
    let m = b.len();
    let mut prod = E::ScalarField::one();
    for j in 0..m {
      let b_j = b[j];
      // iterate from first (msb) to last (lsb) bit of i
      // to build chi_i using the formula above
      if i >> (m - j - 1) & 1 == 1 {
        prod = prod * b_j;
      } else {
        prod = prod * (E::ScalarField::one() - b_j)
      };
    }
    prod
  }

  pub fn open(
    &mut self,
    transcript: &mut PoseidonTranscript<E::ScalarField>,
    comm_list: Vec<Commitment<E>>,
    ck: &CommitterKey<E>,
    point: &[E::ScalarField],
    t: &E::TargetField,
  ) -> (Commitment<E>, Proof<E>, MippProof<E>) {
    let m = point.len() / 2;
    let a = &point[0..m];
    if self.q.is_none() {
      self.get_q(point);
    }

    let q = self.q.clone().unwrap();

    let timer_open = Timer::new("sqrt_open");

    // Compute the PST commitment to q obtained as the inner products of the
    // commitments to the polynomials p_i and chi_i(\vec{b}) for i ranging over
    // the boolean hypercube of size m.
    let _m = a.len();
    let timer_msm = Timer::new("msm");
    if self.chis_b.is_none() {
      panic!("chis(b) should have been computed for q");
    }
    // TODO remove that cloning - the whole option thing
    let chis = self.chis_b.clone().unwrap();
    assert!(chis.len() == comm_list.len());

    let comms: Vec<_> = comm_list.par_iter().map(|c| c.g_product).collect();

    let c_u = <E::G1 as VariableBaseMSM>::msm_unchecked(&comms, &chis).into_affine();
    timer_msm.stop();

    let U: Commitment<E> = Commitment {
      nv: q.num_vars,
      g_product: c_u,
    };
    let comm = MultilinearPC::<E>::commit(ck, &q);
    debug_assert!(c_u == comm.g_product);
    let h_vec = ck.powers_of_h[0].clone();

    // construct MIPP proof that U is the inner product of the vector A
    // and the vector y, where A is the opening vector to T
    let timer_mipp_proof = Timer::new("mipp_prove");
    let mipp_proof =
      MippProof::<E>::prove(transcript, ck, comms, chis.to_vec(), h_vec, &c_u, t).unwrap();
    timer_mipp_proof.stop();

    let timer_proof = Timer::new("pst_open");

    // reversing a is necessary because the sumcheck code in spartan generates
    // the point in reverse order compared to how the polynomial commitment
    // expects it
    let mut a_rev = a.to_vec().clone();
    a_rev.reverse();

    // construct PST proof for opening q at a
    let pst_proof = MultilinearPC::<E>::open(ck, &q, &a_rev);
    timer_proof.stop();

    timer_open.stop();
    (U, pst_proof, mipp_proof)
  }

  pub fn verify(
    transcript: &mut PoseidonTranscript<E::ScalarField>,
    vk: &VerifierKey<E>,
    U: &Commitment<E>,
    point: &[E::ScalarField],
    v: E::ScalarField,
    pst_proof: &Proof<E>,
    mipp_proof: &MippProof<E>,
    T: &E::TargetField,
  ) -> bool {
    let len = point.len();
    let a = &point[0..len / 2];
    let b = &point[len / 2..len];

    let timer_mipp_verify = Timer::new("mipp_verify");
    // verify that U = A^y where A is the opening vector of T
    let res_mipp = MippProof::<E>::verify(vk, transcript, mipp_proof, b.to_vec(), &U.g_product, T);
    assert!(res_mipp == true);
    timer_mipp_verify.stop();

    // reversing a is necessary because the sumcheck code in spartan generates
    // the point in reverse order compared to how the polynomial commitment
    // expects
    let mut a_rev = a.to_vec().clone();
    a_rev.reverse();

    let timer_pst_verify = Timer::new("pst_verify");
    // PST proof that q(a) is indeed equal to value claimed by the prover
    let res = MultilinearPC::<E>::check(vk, U, &a_rev, v, pst_proof);
    timer_pst_verify.stop();
    res
  }
}

#[cfg(test)]
mod tests {

  use crate::parameters::poseidon_params;

  use super::*;
  type F = ark_bls12_377::Fr;
  type E = ark_bls12_377::Bls12_377;

  use ark_std::UniformRand;
  #[test]
  fn check_sqrt_poly_eval() {
    let mut rng = ark_std::test_rng();
    let num_vars = 8;
    let len = 2_usize.pow(num_vars);
    let Z: Vec<F> = (0..len).into_iter().map(|_| F::rand(&mut rng)).collect();
    let r: Vec<F> = (0..num_vars)
      .into_iter()
      .map(|_| F::rand(&mut rng))
      .collect();

    let p = DensePolynomial::new(Z.clone());
    let res1 = p.evaluate(&r);

    let mut pl = Polynomial::<E>::from_evaluations(&Z.clone());
    let res2 = pl.eval(&r);

    assert!(res1 == res2);
  }

  #[test]
  fn check_new_poly_commit() {
    let mut rng = ark_std::test_rng();
    let num_vars = 4;
    let len = 2_usize.pow(num_vars);
    let Z: Vec<F> = (0..len).into_iter().map(|_| F::rand(&mut rng)).collect();
    let r: Vec<F> = (0..num_vars)
      .into_iter()
      .map(|_| F::rand(&mut rng))
      .collect();

    let gens = MultilinearPC::<E>::setup(2, &mut rng);
    let (ck, vk) = MultilinearPC::<E>::trim(&gens, 2);

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
