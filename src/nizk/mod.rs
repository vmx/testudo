#![allow(clippy::too_many_arguments)]
use crate::math::Math;
use crate::poseidon_transcript::PoseidonTranscript;

use super::commitments::{Commitments, MultiCommitGens};
use super::errors::ProofVerifyError;
use ark_ec::CurveGroup;

use ark_serialize::*;
use std::ops::Mul;

mod bullet;
use bullet::BulletReductionProof;

#[derive(Clone)]
pub struct DotProductProofGens<G: CurveGroup> {
  n: usize,
  pub gens_n: MultiCommitGens<G>,
  pub gens_1: MultiCommitGens<G>,
}

impl<G: CurveGroup> DotProductProofGens<G> {
  pub fn new(n: usize, label: &[u8]) -> Self {
    let (gens_n, gens_1) = MultiCommitGens::<G>::new(n + 1, label).split_at(n);
    DotProductProofGens { n, gens_n, gens_1 }
  }
}

#[derive(Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct DotProductProofLog<G: CurveGroup> {
  bullet_reduction_proof: BulletReductionProof<G>,
  delta: G,
  beta: G,
  z1: G::ScalarField,
  z2: G::ScalarField,
}

impl<G: CurveGroup> DotProductProofLog<G> {
  fn protocol_name() -> &'static [u8] {
    b"dot product proof (log)"
  }

  pub fn compute_dotproduct(a: &[G], b: &[G]) -> G {
    assert_eq!(a.len(), b.len());
    (0..a.len()).map(|i| a[i] * b[i]).sum()
  }

  pub fn prove(
    gens: &DotProductProofGens<G>,
    transcript: &mut PoseidonTranscript<G::ScalarField>,
    x_vec: &[G::ScalarField],
    blind_x: &G::ScalarField,
    a_vec: &[G::ScalarField],
    y: &G::ScalarField,
    blind_y: &G::ScalarField,
  ) -> (Self, G, G) {
    // transcript.append_protocol_name(DotProductProofLog::protocol_name());

    let n = x_vec.len();
    assert_eq!(x_vec.len(), a_vec.len());
    assert_eq!(gens.n, n);

    // produce randomness for generating a proof
    let d = G::ScalarField::rand(&mut rand::thread_rng()).into();
    let r_delta = G::ScalarField::rand(&mut rand::thread_rng()).into();
    let r_beta = G::ScalarField::rand(&mut rand::thread_rng()).into();
    let blinds_vec = {
      let v1 = (0..2 * n.log_2())
        .map(|_| {
          (
            G::ScalarField::rand(&mut rand::thread_rng()).into(),
            G::ScalarField::rand(&mut rand::thread_rng()).into(),
          )
        })
        .collect::<Vec<(G::ScalarField, G::ScalarField)>>();
    };

    let Cx = x_vec.commit(blind_x, &gens.gens_n).compress();
    transcript.append_point(&Cx);

    let Cy = y.commit(blind_y, &gens.gens_1).compress();
    transcript.append_point(&Cy);
    transcript.append_scalar_vector(a_vec);

    let blind_Gamma = (*blind_x) + blind_y;
    let (bullet_reduction_proof, _Gamma_hat, x_hat, a_hat, g_hat, rhat_Gamma) =
      BulletReductionProof::prove(
        transcript,
        &gens.gens_1.G[0],
        &gens.gens_n.G,
        &gens.gens_n.h,
        x_vec,
        a_vec,
        &blind_Gamma,
        &blinds_vec,
      );
    let y_hat = x_hat * a_hat;

    let delta = {
      let gens_hat = MultiCommitGens {
        n: 1,
        G: vec![g_hat],
        h: gens.gens_1.h,
      };
      d.commit(&r_delta, &gens_hat).compress()
    };
    transcript.append_point(&delta);

    let beta = d.commit(&r_beta, &gens.gens_1).compress();
    transcript.append_point(&beta);

    let c = transcript.challenge_scalar();

    let z1 = d + c * y_hat;
    let z2 = a_hat * (c * rhat_Gamma + r_beta) + r_delta;

    (
      Self {
        bullet_reduction_proof,
        delta,
        beta,
        z1,
        z2,
      },
      Cx,
      Cy,
    )
  }

  pub fn verify(
    &self,
    n: usize,
    gens: &DotProductProofGens<G>,
    transcript: &mut PoseidonTranscript<G::ScalarField>,
    a: &[G::ScalarField],
    Cx: &G,
    Cy: &G,
  ) -> Result<(), ProofVerifyError> {
    assert_eq!(gens.n, n);
    assert_eq!(a.len(), n);

    // transcript.append_protocol_name(DotProductProofLog::protocol_name());
    // Cx.append_to_poseidon( transcript);
    // Cy.append_to_poseidon( transcript);
    // a.append_to_poseidon( transcript);

    transcript.append_point(Cx);
    transcript.append_point(Cy);
    transcript.append_scalar_vector(a);

    let Gamma = Cx + Cy;

    let (g_hat, Gamma_hat, a_hat) =
      self
        .bullet_reduction_proof
        .verify(n, a, transcript, &Gamma, &gens.gens_n.G)?;
    // self.delta.append_to_poseidon( transcript);
    // self.beta.append_to_poseidon( transcript);

    transcript.append_point(&self.delta);
    transcript.append_point(&self.beta);

    let c = transcript.challenge_scalar();

    let c_s = &c;
    let beta_s = self.beta;
    let a_hat_s = &a_hat;
    let delta_s = self.delta;
    let z1_s = &self.z1;
    let z2_s = &self.z2;

    let lhs = (Gamma_hat.mul(c_s) + beta_s).mul(a_hat_s) + delta_s;
    let rhs =
      (g_hat + gens.gens_1.G[0].mul(a_hat_s)).mul(z1_s) + gens.gens_1.h.mul(z2_s);

    assert_eq!(lhs, rhs);

    if lhs == rhs {
      Ok(())
    } else {
      Err(ProofVerifyError::InternalError)
    }
  }
}

#[cfg(test)]
mod tests {

  use crate::parameters::poseidon_params;

  use super::*;
  use ark_std::UniformRand;
  type F = ark_bls12_377::Fr;
  

  #[test]
  fn check_dotproductproof_log() {
    let mut rng = ark_std::rand::thread_rng();

    let n = 1024;

    let gens = DotProductProofGens::new(n, b"test-1024");

    let x: Vec<F> = (0..n).map(|_i| F::rand(&mut rng)).collect();
    let a: Vec<F> = (0..n).map(|_i| F::rand(&mut rng)).collect();
    let y = DotProductProofLog::compute_dotproduct(&x, &a);

    let r_x = F::rand(&mut rng);
    let r_y = F::rand(&mut rng);

    let params = poseidon_params();
    let mut prover_transcript = PoseidonTranscript::new(&params);
    let (proof, Cx, Cy) = DotProductProofLog::prove(
      &gens,
      &mut prover_transcript,
      &x,
      &r_x,
      &a,
      &y,
      &r_y,
    );

    let mut verifier_transcript = PoseidonTranscript::new(&params);
    assert!(proof
      .verify(n, &gens, &mut verifier_transcript, &a, &Cx, &Cy)
      .is_ok());
  }
}
