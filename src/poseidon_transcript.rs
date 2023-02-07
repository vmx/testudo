use super::scalar::Scalar;
use crate::group::{CompressedGroup, Fr};
use crate::mipp::Transcript;
use ark_bls12_377::{Bls12_377 as I, G1Affine};
use ark_crypto_primitives::sponge::{
  poseidon::{PoseidonConfig, PoseidonSponge},
  CryptographicSponge,
};
use ark_ec::pairing::Pairing;
use ark_ff::{PrimeField};
use ark_poly_commit::multilinear_pc::data_structures::Commitment;
use ark_serialize::CanonicalSerialize;
use ark_serialize::Compress;
#[derive(Clone)]
/// TODO
pub struct PoseidonTranscript {
  sponge: PoseidonSponge<Fr>,
  params: PoseidonConfig<Fr>,
}

impl Transcript for PoseidonTranscript {
  fn domain_sep(&mut self) {
    self.sponge.absorb(&b"testudo".to_vec());
  }

  fn append<S: CanonicalSerialize>(&mut self, _label: &'static [u8], point: &S) {
    let mut buf = Vec::new();
    point
      .serialize_with_mode(&mut buf, Compress::Yes)
      .expect("serialization failed");
    self.sponge.absorb(&buf);
  }

  fn challenge_scalar<F: PrimeField>(&mut self, _label: &'static [u8]) -> F {
    self.sponge.squeeze_field_elements(1).remove(0)
  }
}

impl PoseidonTranscript {
  /// create a new transcript
  pub fn new(params: &PoseidonConfig<Fr>) -> Self {
    let sponge = PoseidonSponge::new(params);
    PoseidonTranscript {
      sponge,
      params: params.clone(),
    }
  }

  pub fn new_from_state(&mut self, challenge: &Scalar) {
    self.sponge = PoseidonSponge::new(&self.params);
    self.append_scalar(challenge);
  }

  pub fn append_u64(&mut self, x: u64) {
    self.sponge.absorb(&x);
  }

  // pub fn append_usize

  pub fn append_bytes(&mut self, x: &Vec<u8>) {
    self.sponge.absorb(x);
  }

  pub fn append_scalar(&mut self, scalar: &Scalar) {
    self.sponge.absorb(&scalar);
  }

  pub fn append_point(&mut self, point: &CompressedGroup) {
    self.sponge.absorb(&point.0);
  }

  pub fn append_scalar_vector(&mut self, scalars: &[Scalar]) {
    for scalar in scalars.iter() {
      self.append_scalar(scalar);
    }
  }

  pub fn append_gt(&mut self, g_t: &<I as Pairing>::TargetField) {
    let mut bytes = Vec::new();
    g_t.serialize_with_mode(&mut bytes, Compress::Yes).unwrap();
    self.append_bytes(&bytes);
  }

  pub fn challenge_scalar(&mut self) -> Scalar {
    self.sponge.squeeze_field_elements(1).remove(0)
  }

  pub fn challenge_vector(&mut self, len: usize) -> Vec<Scalar> {
    self.sponge.squeeze_field_elements(len)
  }
}

pub trait AppendToPoseidon {
  fn append_to_poseidon(&self, transcript: &mut PoseidonTranscript);
}

impl AppendToPoseidon for CompressedGroup {
  fn append_to_poseidon(&self, transcript: &mut PoseidonTranscript) {
    transcript.append_point(self);
  }
}

impl AppendToPoseidon for Commitment<I> {
  fn append_to_poseidon(&self, transcript: &mut PoseidonTranscript) {
    let mut bytes = Vec::new();
    self.serialize_with_mode(&mut bytes, Compress::Yes).unwrap();
    transcript.append_bytes(&bytes);
  }
}

impl AppendToPoseidon for G1Affine {
  fn append_to_poseidon(&self, transcript: &mut PoseidonTranscript) {
    let mut bytes = Vec::new();
    self.serialize_with_mode(&mut bytes, Compress::Yes).unwrap();
    transcript.append_bytes(&bytes);
  }
}
