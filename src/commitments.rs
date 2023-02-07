use super::group::{GroupElement, GroupElementAffine, VartimeMultiscalarMul, GROUP_BASEPOINT};
use super::scalar::Scalar;
use crate::group::CompressGroupElement;
use crate::parameters::*;
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::PrimeField;
use std::ops::Mul;

use ark_crypto_primitives::sponge::poseidon::PoseidonSponge;
use ark_crypto_primitives::sponge::CryptographicSponge;

#[derive(Debug, Clone)]
pub struct MultiCommitGens<G: CurveGroup> {
  pub n: usize,
  pub G: Vec<G::Affine>,
  pub h: G::Affine,
}

impl<G: CurveGroup> MultiCommitGens<G> {
  pub fn new(n: usize, label: &[u8]) -> Self {
    let params = poseidon_params();
    let mut sponge = PoseidonSponge::new(&params);
    sponge.absorb(&label);
    sponge.absorb(&GROUP_BASEPOINT.compress().0);

    let gens = (0..=n)
      .map(|i| {
        let mut el_aff: Option<GroupElementAffine> = None;
        while el_aff.is_none() {
          let uniform_bytes = sponge.squeeze_bytes(64);
          el_aff = GroupElementAffine::from_random_bytes(&uniform_bytes);
        }
        el_aff.unwrap().clear_cofactor()
      })
      .collect::<Vec<_>>();

    MultiCommitGens {
      n,
      G: gens[..n].to_vec(),
      h: gens[n],
    }
  }

  pub fn clone(&self) -> Self {
    MultiCommitGens {
      n: self.n,
      h: self.h,
      G: self.G.clone(),
    }
  }

  pub fn split_at(&self, mid: usize) -> (Self, Self) {
    let (G1, G2) = self.G.split_at(mid);

    (
      MultiCommitGens {
        n: G1.len(),
        G: G1.to_vec(),
        h: self.h,
      },
      MultiCommitGens {
        n: G2.len(),
        G: G2.to_vec(),
        h: self.h,
      },
    )
  }
}

// TODO replace that by arkworks CommitmentScheme probably exists
pub trait Commitments<G: CurveGroup> {
  fn commit(&self, blind: &G::ScalarField, gens_n: &MultiCommitGens<G>) -> G;
}

impl<G: CurveGroup> Commitments<G> for G::ScalarField {
  fn commit(&self, blind: &G::ScalarField, gens_n: &MultiCommitGens<G>) -> G {
    assert_eq!(gens_n.n, 1);
    <G as VariableBaseMSM>::msm(&[*self, *blind], &[gens_n.G[0], gens_n.h])
  }
}

impl<G: CurveGroup> Commitments<G> for Vec<G::ScalarField> {
  fn commit(&self, blind: &G::ScalarField, gens_n: &MultiCommitGens<G>) -> G {
    assert_eq!(gens_n.n, self.len());
    <G as VariableBaseMSM>::msm(self, &gens_n.G) + gens_n.h.mul(blind)
  }
}

impl<G: CurveGroup> Commitments<G> for [G::ScalarField] {
  fn commit(&self, blind: &G::ScalarField, gens_n: &MultiCommitGens<G>) -> G {
    assert_eq!(gens_n.n, self.len());
    <G as VariableBaseMSM>::msm(self, &gens_n.G) + gens_n.h.mul(blind)
  }
}
