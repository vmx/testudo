use crate::parameters::*;
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};

use ark_crypto_primitives::sponge::poseidon::PoseidonSponge;
use ark_crypto_primitives::sponge::CryptographicSponge;
use std::ops::Mul;

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
    let mut b = Vec::new();
    G::generator().serialize_compressed(&mut b).unwrap();
    sponge.absorb(&b);

    let gens = (0..=n)
      .map(|i| {
        let mut el_aff: Option<G::Affine> = None;
        while el_aff.is_none() {
          let uniform_bytes = sponge.squeeze_bytes(64);
          el_aff = G::Affine::from_random_bytes(&uniform_bytes);
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

pub struct PedersenCommit;

impl PedersenCommit {
  pub fn commit_scalar<G: CurveGroup>(
    scalar: &G::ScalarField,
    blind: &G::ScalarField,
    gens_n: &MultiCommitGens<G>,
  ) -> G {
    assert_eq!(gens_n.n, 1);
    <G as VariableBaseMSM>::msm_unchecked(&[gens_n.G[0], gens_n.h], &[*scalar, *blind])
  }

  pub fn commit_slice<G: CurveGroup>(
    scalars: &[G::ScalarField],
    blind: &G::ScalarField,
    gens_n: &MultiCommitGens<G>,
  ) -> G {
    assert_eq!(scalars.len(), gens_n.n);
    <G as VariableBaseMSM>::msm_unchecked(&gens_n.G, scalars) + gens_n.h.mul(blind)
  }
}