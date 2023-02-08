use crate::transcript::Transcript;
use ark_crypto_primitives::sponge::{
  poseidon::{PoseidonConfig, PoseidonSponge},
  Absorb, CryptographicSponge,
};
use ark_ec::{pairing::Pairing, CurveGroup};
use ark_ff::PrimeField;
use ark_serialize::CanonicalSerialize;
use ark_serialize::Compress;
#[derive(Clone)]
/// TODO
pub struct PoseidonTranscript<F: PrimeField> {
  sponge: PoseidonSponge<F>,
  params: PoseidonConfig<F>,
}

impl<F: PrimeField> Transcript for PoseidonTranscript<F> {
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

  fn challenge_scalar<FF: PrimeField>(&mut self, _label: &'static [u8]) -> FF {
    self.sponge.squeeze_field_elements(1).remove(0)
  }
}

impl<F: PrimeField> PoseidonTranscript<F> {
  /// create a new transcript
  pub fn new(params: &PoseidonConfig<F>) -> Self {
    let sponge = PoseidonSponge::new(params);
    PoseidonTranscript {
      sponge,
      params: params.clone(),
    }
  }

  pub fn new_from_state(&mut self, challenge: &F) {
    self.sponge = PoseidonSponge::new(&self.params);
    self.append(b"", challenge);
  }
  pub fn append_u64(&mut self, _label: &'static [u8], x: u64) {
    self.sponge.absorb(&x);
  }

  pub fn append_bytes(&mut self, _label: &'static [u8], x: &Vec<u8>) {
    self.sponge.absorb(x);
  }

  pub fn append_scalar<T: PrimeField + Absorb>(&mut self, _label: &'static [u8], scalar: &T) {
    self.sponge.absorb(&scalar);
  }

  pub fn append_point<G>(&mut self, _label: &'static [u8], point: &G)
  where
    G: CurveGroup,
  {
    let mut point_encoding = Vec::new();
    point
      .serialize_with_mode(&mut point_encoding, Compress::Yes)
      .unwrap();
    self.sponge.absorb(&point_encoding);
  }

  pub fn append_scalar_vector<T: PrimeField + Absorb>(
    &mut self,
    _label: &'static [u8],
    scalars: &[T],
  ) {
    for scalar in scalars.iter() {
      self.append_scalar(b"", scalar);
    }
  }

  pub fn append_gt<E>(&mut self, _label: &'static [u8], g_t: &E::TargetField)
  where
    E: Pairing,
  {
    let mut bytes = Vec::new();
    g_t.serialize_with_mode(&mut bytes, Compress::Yes).unwrap();
    self.append_bytes(b"", &bytes);
  }
}

pub trait TranscriptWriter<F: PrimeField> {
  fn write_to_transcript(&self, transcript: &mut PoseidonTranscript<F>);
}
//pub trait AppendToPoseidon {
//  fn append_to_poseidon(&self, transcript: &mut PoseidonTranscript);
//}
//
//impl AppendToPoseidon for CompressedGroup {
//  fn append_to_poseidon(&self, transcript: &mut PoseidonTranscript) {
//    transcript.append_point(self);
//  }
//}
//
//impl AppendToPoseidon for Commitment<I> {
//  fn append_to_poseidon(&self, transcript: &mut PoseidonTranscript) {
//    let mut bytes = Vec::new();
//    self.serialize_with_mode(&mut bytes, Compress::Yes).unwrap();
//    transcript.append_bytes(&bytes);
//  }
//}
//
//impl AppendToPoseidon for G1Affine {
//  fn append_to_poseidon(&self, transcript: &mut PoseidonTranscript) {
//    let mut bytes = Vec::new();
//    self.serialize_with_mode(&mut bytes, Compress::Yes).unwrap();
//    transcript.append_bytes(&bytes);
//}
//
