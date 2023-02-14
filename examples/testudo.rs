use std::time::Instant;

use ark_blst::{Bls12, Scalar};
use ark_serialize::CanonicalSerialize;
use libspartan::{
  parameters::PoseidonConfiguration,
  poseidon_transcript::PoseidonTranscript,
  testudo_snark::{TestudoSnark, TestudoSnarkGens},
  Instance,
};
use log::debug;

fn main() {
  fil_logger::maybe_init();

  let num_vars = 1 << 10;
  let num_cons = num_vars;
  let num_inputs = 328;

  debug!("vmx: start");
  let (inst, vars, inputs) = Instance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);
  let params = Scalar::poseidon_params();
  let mut prover_transcript = PoseidonTranscript::new(&params);

  debug!("vmx: key generation: start");
  let gens =
    TestudoSnarkGens::<Bls12>::new(num_cons, num_vars, num_inputs, num_cons, params.clone());
  debug!("vmx: key generation: stop");

  let (comm, decomm) = TestudoSnark::encode(&inst, &gens);

  let start = Instant::now();
  let proof = TestudoSnark::prove(
    &inst,
    &comm,
    &decomm,
    vars,
    &inputs,
    &gens,
    &mut prover_transcript,
    params.clone(),
  )
  .unwrap();
  let duration = start.elapsed().as_millis();
  debug!("proving time: {}ms", duration);

  let mut verifier_transcript = PoseidonTranscript::new(&params);
  let start = Instant::now();

  let res = proof.verify(&gens, &comm, &inputs, &mut verifier_transcript, params);
  assert!(res.is_ok());
  let duration = start.elapsed().as_millis();
  debug!("verification time: {}", duration);
}
