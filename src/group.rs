use crate::errors::ProofVerifyError;
use ark_ec::scalar_mul::variable_base::VariableBaseMSM;
use ark_ec::Group;
use ark_ff::PrimeField;
use lazy_static::lazy_static;

use super::scalar::Scalar;

use ark_ec::CurveGroup;
use ark_serialize::*;
use core::borrow::Borrow;

pub type GroupElement = ark_bls12_377::G1Projective;
pub type GroupElementAffine = ark_bls12_377::G1Affine;
pub type Fq = ark_bls12_377::Fq;
pub type Fr = ark_bls12_377::Fr;

#[derive(Clone, Eq, PartialEq, Hash, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct CompressedGroup(pub Vec<u8>);

lazy_static! {
  pub static ref GROUP_BASEPOINT: GroupElement = GroupElement::generator();
}

pub trait CompressGroupElement {
  fn compress(&self) -> CompressedGroup;
}

pub trait DecompressGroupElement {
  fn decompress(encoded: &CompressedGroup) -> Option<GroupElement>;
}

pub trait UnpackGroupElement {
  fn unpack(&self) -> Result<GroupElement, ProofVerifyError>;
}

impl CompressGroupElement for GroupElement {
  fn compress(&self) -> CompressedGroup {
    let mut point_encoding = Vec::new();
    self
      .serialize_with_mode(&mut point_encoding, Compress::Yes)
      .unwrap();
    CompressedGroup(point_encoding)
  }
}

impl DecompressGroupElement for GroupElement {
  fn decompress(encoded: &CompressedGroup) -> Option<Self> {
    let res = GroupElement::deserialize_compressed(&*encoded.0);
    if let Ok(r) = res {
      Some(r)
    } else {
      println!("{:?}", res);
      None
    }
  }
}

impl UnpackGroupElement for CompressedGroup {
  fn unpack(&self) -> Result<GroupElement, ProofVerifyError> {
    let encoded = self.0.clone();
    GroupElement::decompress(self).ok_or(ProofVerifyError::DecompressionError(encoded))
  }
}

pub trait VartimeMultiscalarMul {
  fn vartime_multiscalar_mul(scalars: &[Scalar], points: &[GroupElement]) -> GroupElement;
}

impl VartimeMultiscalarMul for GroupElement {
  fn vartime_multiscalar_mul(scalars: &[Scalar], points: &[GroupElement]) -> GroupElement {
    assert!(scalars.len() == points.len());
    let aff_points = points
      .iter()
      .map(|P| P.borrow().into_affine())
      .collect::<Vec<GroupElementAffine>>();
    <Self as VariableBaseMSM>::msm_unchecked(aff_points.as_slice(), scalars)
  }
}
