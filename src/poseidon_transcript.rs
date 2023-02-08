use crate::transcript::Transcript;
use ark_crypto_primitives::sponge::{
  poseidon::{PoseidonConfig, PoseidonSponge},
  CryptographicSponge,
};
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
    self.append(b"",challenge);
  }
}
