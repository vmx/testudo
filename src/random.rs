use super::scalar::Scalar;
use crate::{parameters::poseidon_params, poseidon_transcript::PoseidonTranscript};
use ark_std::UniformRand;

pub struct RandomTape {
  tape: PoseidonTranscript,
}

impl RandomTape {
  pub fn new(_name: &'static [u8]) -> Self {
    let tape = {
      let mut rng = ark_std::rand::thread_rng();
      let mut tape = PoseidonTranscript::new(&poseidon_params());
      tape.append_scalar(&Scalar::rand(&mut rng));
      tape
    };
    Self { tape }
  }

  pub fn random_scalar(&mut self, _label: &'static [u8]) -> Scalar {
    self.tape.challenge_scalar()
  }

  pub fn random_vector(&mut self, _label: &'static [u8], len: usize) -> Vec<Scalar> {
    self.tape.challenge_vector(len)
  }
}
