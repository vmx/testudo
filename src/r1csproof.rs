#![allow(clippy::too_many_arguments)]
use super::dense_mlpoly::{DensePolynomial, EqPolynomial, PolyCommitmentGens};
use super::errors::ProofVerifyError;
use crate::constraints::{R1CSVerificationCircuit, VerifierConfig};
use crate::math::Math;
use crate::mipp::MippProof;
use crate::poseidon_transcript::PoseidonTranscript;
use crate::sqrt_pst::Polynomial;
use crate::sumcheck::SumcheckInstanceProof;
use crate::transcript::{Transcript};
use ark_crypto_primitives::sponge::poseidon::PoseidonConfig;
use ark_ec::pairing::Pairing;

use ark_poly_commit::multilinear_pc::data_structures::{Commitment, Proof};

use super::r1csinstance::R1CSInstance;

use super::sparse_mlpoly::{SparsePolyEntry, SparsePolynomial};
use super::timer::Timer;
use ark_snark::{CircuitSpecificSetupSNARK, SNARK};

use ark_groth16::Groth16;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
use ark_serialize::*;
use ark_std::{One, Zero};

use std::time::Instant;

#[derive(CanonicalSerialize, CanonicalDeserialize, Debug)]
pub struct R1CSProof<E: Pairing> {
  // The PST commitment to the multilinear extension of the witness.
  comm: Commitment<E>,
  sc_proof_phase1: SumcheckInstanceProof<E::ScalarField>,
  claims_phase2: (
    E::ScalarField,
    E::ScalarField,
    E::ScalarField,
    E::ScalarField,
  ),
  sc_proof_phase2: SumcheckInstanceProof<E::ScalarField>,
  eval_vars_at_ry: E::ScalarField,
  proof_eval_vars_at_ry: Proof<E>,
  rx: Vec<E::ScalarField>,
  ry: Vec<E::ScalarField>,
  // The transcript state after the satisfiability proof was computed.
  pub transcript_sat_state: E::ScalarField,
  pub t: E::TargetField,
  pub mipp_proof: MippProof<E>,
}

#[derive(Clone)]
pub struct R1CSGens<E: Pairing> {
  gens_pc: PolyCommitmentGens<E>,
}

impl<E: Pairing> R1CSGens<E> {
  pub fn new(label: &'static [u8], _num_cons: usize, num_vars: usize) -> Self {
    let num_poly_vars = num_vars.log_2();
    let gens_pc = PolyCommitmentGens::new(num_poly_vars, label);
    R1CSGens { gens_pc }
  }
}

impl<E: Pairing> R1CSProof<E> {
  fn prove_phase_one(
    num_rounds: usize,
    evals_tau: &mut DensePolynomial<E::ScalarField>,
    evals_Az: &mut DensePolynomial<E::ScalarField>,
    evals_Bz: &mut DensePolynomial<E::ScalarField>,
    evals_Cz: &mut DensePolynomial<E::ScalarField>,
    transcript: &mut PoseidonTranscript<E::ScalarField>,
  ) -> (
    SumcheckInstanceProof<E::ScalarField>,
    Vec<E::ScalarField>,
    Vec<E::ScalarField>,
  ) {
    let comb_func =
      |poly_tau_comp: &E::ScalarField,
       poly_A_comp: &E::ScalarField,
       poly_B_comp: &E::ScalarField,
       poly_C_comp: &E::ScalarField|
       -> E::ScalarField { (*poly_tau_comp) * ((*poly_A_comp) * poly_B_comp - poly_C_comp) };

    let (sc_proof_phase_one, r, claims) = SumcheckInstanceProof::prove_cubic_with_additive_term(
      &E::ScalarField::zero(), // claim is zero
      num_rounds,
      evals_tau,
      evals_Az,
      evals_Bz,
      evals_Cz,
      comb_func,
      transcript,
    );

    (sc_proof_phase_one, r, claims)
  }

  fn prove_phase_two(
    num_rounds: usize,
    claim: &E::ScalarField,
    evals_z: &mut DensePolynomial<E::ScalarField>,
    evals_ABC: &mut DensePolynomial<E::ScalarField>,
    transcript: &mut PoseidonTranscript<E::ScalarField>,
  ) -> (
    SumcheckInstanceProof<E::ScalarField>,
    Vec<E::ScalarField>,
    Vec<E::ScalarField>,
  ) {
    let comb_func = |poly_A_comp: &E::ScalarField,
                     poly_B_comp: &E::ScalarField|
     -> E::ScalarField { (*poly_A_comp) * poly_B_comp };
    let (sc_proof_phase_two, r, claims) = SumcheckInstanceProof::prove_quad(
      claim, num_rounds, evals_z, evals_ABC, comb_func, transcript,
    );

    (sc_proof_phase_two, r, claims)
  }


  pub fn prove(
    inst: &R1CSInstance<E::ScalarField>,
    vars: Vec<E::ScalarField>,
    input: &[E::ScalarField],
    gens: &R1CSGens<E>,
    transcript: &mut PoseidonTranscript<E::ScalarField>,
  ) -> (Self, Vec<E::ScalarField>, Vec<E::ScalarField>) {
    let timer_prove = Timer::new("R1CSProof::prove");
    // we currently require the number of |inputs| + 1 to be at most number of vars
    assert!(input.len() < vars.len());

    // create the multilinear witness polynomial from the satisfying assiment
    // expressed as the list of sqrt-sized polynomials
    let mut pl = Polynomial::from_evaluations(&vars.clone());

    let timer_commit = Timer::new("polycommit");

    // commitment list to the satisfying witness polynomial list
    let (comm_list, t) = pl.commit(&gens.gens_pc.ck);

    let mut bytes = Vec::new();
    t.serialize_with_mode(&mut bytes, Compress::Yes).unwrap();
    transcript.append(b"", &bytes);

    // comm.write_to_transcript(transcript);
    timer_commit.stop();

    let c = transcript.challenge_scalar(b"");
    transcript.new_from_state(&c);

    transcript.append(b"", &input);

    let timer_sc_proof_phase1 = Timer::new("prove_sc_phase_one");

    // append input to variables to create a single vector z
    let z = {
      let num_inputs = input.len();
      let num_vars = vars.len();
      let mut z = vars;
      z.extend(&vec![E::ScalarField::one()]); // add constant term in z
      z.extend(input);
      z.extend(&vec![E::ScalarField::zero(); num_vars - num_inputs - 1]); // we will pad with zeros
      z
    };

    // derive the verifier's challenge tau
    let (num_rounds_x, num_rounds_y) = (inst.get_num_cons().log_2(), z.len().log_2());
    let tau = transcript.challenge_scalar_vec(b"", num_rounds_x);
    // compute the initial evaluation table for R(\tau, x)
    let mut poly_tau = DensePolynomial::new(EqPolynomial::new(tau).evals());
    let (mut poly_Az, mut poly_Bz, mut poly_Cz) =
      inst.multiply_vec(inst.get_num_cons(), z.len(), &z);

    let (sc_proof_phase1, rx, _claims_phase1) = R1CSProof::<E>::prove_phase_one(
      num_rounds_x,
      &mut poly_tau,
      &mut poly_Az,
      &mut poly_Bz,
      &mut poly_Cz,
      transcript,
    );
    assert_eq!(poly_tau.len(), 1);
    assert_eq!(poly_Az.len(), 1);
    assert_eq!(poly_Bz.len(), 1);
    assert_eq!(poly_Cz.len(), 1);
    timer_sc_proof_phase1.stop();

    let (tau_claim, Az_claim, Bz_claim, Cz_claim) =
      (&poly_tau[0], &poly_Az[0], &poly_Bz[0], &poly_Cz[0]);
    let prod_Az_Bz_claims = (*Az_claim) * Bz_claim;

    // prove the final step of sum-check #1
    let taus_bound_rx = tau_claim;
    let _claim_post_phase1 = ((*Az_claim) * Bz_claim - Cz_claim) * taus_bound_rx;

    let timer_sc_proof_phase2 = Timer::new("prove_sc_phase_two");
    // combine the three claims into a single claim
    let r_A: E::ScalarField = transcript.challenge_scalar(b"");
    let r_B: E::ScalarField = transcript.challenge_scalar(b"");
    let r_C: E::ScalarField = transcript.challenge_scalar(b"");
    let claim_phase2 = r_A * Az_claim + r_B * Bz_claim + r_C * Cz_claim;

    let evals_ABC = {
      // compute the initial evaluation table for R(\tau, x)
      let evals_rx = EqPolynomial::new(rx.clone()).evals();
      let (evals_A, evals_B, evals_C) =
        inst.compute_eval_table_sparse(inst.get_num_cons(), z.len(), &evals_rx);

      assert_eq!(evals_A.len(), evals_B.len());
      assert_eq!(evals_A.len(), evals_C.len());
      (0..evals_A.len())
        .map(|i| r_A * evals_A[i] + r_B * evals_B[i] + r_C * evals_C[i])
        .collect::<Vec<_>>()
    };

    // another instance of the sum-check protocol
    let (sc_proof_phase2, ry, _claims_phase2) = R1CSProof::<E>::prove_phase_two(
      num_rounds_y,
      &claim_phase2,
      &mut DensePolynomial::new(z),
      &mut DensePolynomial::new(evals_ABC),
      transcript,
    );
    timer_sc_proof_phase2.stop();
    let c = transcript.challenge_scalar(b"");
    transcript.new_from_state(&c);

    // TODO: modify the polynomial evaluation in Spartan to be consistent
    // with the evaluation in ark-poly-commit so that reversing is not needed
    // anymore
    let timmer_opening = Timer::new("polyopening");

    let (comm, proof_eval_vars_at_ry, mipp_proof) =
      pl.open(transcript, comm_list, &gens.gens_pc.ck, &ry[1..], &t);
    println!(
      "proof size (no of quotients): {:?}",
      proof_eval_vars_at_ry.proofs.len()
    );

    timmer_opening.stop();

    let timer_polyeval = Timer::new("polyeval");
    let eval_vars_at_ry = pl.eval(&ry[1..]);
    timer_polyeval.stop();
    timer_prove.stop();
    (
      R1CSProof {
        comm,
        sc_proof_phase1,
        claims_phase2: (*Az_claim, *Bz_claim, *Cz_claim, prod_Az_Bz_claims),
        sc_proof_phase2,
        eval_vars_at_ry,
        proof_eval_vars_at_ry,
        rx: rx.clone(),
        ry: ry.clone(),
        transcript_sat_state: c,
        t,
        mipp_proof,
      },
      rx,
      ry,
    )
  }

  pub fn verify_groth16(
    &self,
    num_vars: usize,
    num_cons: usize,
    input: &[E::ScalarField],
    evals: &(E::ScalarField, E::ScalarField, E::ScalarField),
    transcript: &mut PoseidonTranscript<E::ScalarField>,
    gens: &R1CSGens<E>,
    poseidon: PoseidonConfig<E::ScalarField>,
  ) -> Result<(u128, u128, u128), ProofVerifyError> {
    // serialise and add the IPP commitment to the transcript
    let mut bytes = Vec::new();
    self
      .t
      .serialize_with_mode(&mut bytes, Compress::Yes)
      .unwrap();
    transcript.append(b"", &bytes);

    let c = transcript.challenge_scalar(b"");

    let mut input_as_sparse_poly_entries = vec![SparsePolyEntry::new(0, E::ScalarField::one())];
    //remaining inputs
    input_as_sparse_poly_entries.extend(
      (0..input.len())
        .map(|i| SparsePolyEntry::new(i + 1, input[i]))
        .collect::<Vec<SparsePolyEntry<E::ScalarField>>>(),
    );

    let n = num_vars;
    let input_as_sparse_poly =
      SparsePolynomial::new(n.log_2() as usize, input_as_sparse_poly_entries);

    let config = VerifierConfig {
      num_vars,
      num_cons,
      input: input.to_vec(),
      evals: *evals,
      params: poseidon,
      prev_challenge: c,
      claims_phase2: self.claims_phase2,
      polys_sc1: self.sc_proof_phase1.polys.clone(),
      polys_sc2: self.sc_proof_phase2.polys.clone(),
      eval_vars_at_ry: self.eval_vars_at_ry,
      input_as_sparse_poly,
      comm: self.comm.clone(),
      ry: self.ry.clone(),
      transcript_sat_state: self.transcript_sat_state,
    };

    let circuit = R1CSVerificationCircuit::new(&config);

    // this is universal, we don't measure it
    // TODO put this _outside_ the verification
    let start = Instant::now();
    let (pk, vk) = Groth16::<E>::setup(circuit.clone(), &mut rand::thread_rng()).unwrap();
    let ds = start.elapsed().as_millis();

    let prove_outer = Timer::new("provecircuit");
    let start = Instant::now();
    let proof = Groth16::<E>::prove(&pk, circuit, &mut rand::thread_rng()).unwrap();
    let dp = start.elapsed().as_millis();
    prove_outer.stop();

    let timer_verification = Timer::new("verification");
    let start = Instant::now();

    /// TODO : they are not necessary ?
    let (v_A, v_B, v_C, v_AB) = self.claims_phase2;

    let mut pubs = vec![];
    pubs.extend(self.ry.clone());
    pubs.extend(vec![self.eval_vars_at_ry, self.transcript_sat_state]);

    transcript.new_from_state(&self.transcript_sat_state);
    par! {
      // verifies the Groth16 proof for the spartan verifier
      let is_verified = Groth16::<E>::verify(&vk, &pubs, &proof).unwrap(),

      // verifies the proof of opening against the result of evaluating the
      // witness polynomial at point ry
      let res = Polynomial::verify(
      transcript,
      &gens.gens_pc.vk,
      &self.comm,
      &self.ry[1..],
      self.eval_vars_at_ry,
      &self.proof_eval_vars_at_ry,
      &self.mipp_proof,
      &self.t,
    )
    };
    let dv = start.elapsed().as_millis();
    timer_verification.stop();

    assert!(res == true && is_verified == true);

    Ok((ds, dp, dv))
  }

  // Helper function to find the number of constraint in the circuit which
  // requires executing it.
  pub fn circuit_size(
    &self,
    num_vars: usize,
    num_cons: usize,
    input: &[E::ScalarField],
    evals: &(E::ScalarField, E::ScalarField, E::ScalarField),
    transcript: &mut PoseidonTranscript<E::ScalarField>,
    _gens: &R1CSGens<E>,
    poseidon: PoseidonConfig<E::ScalarField>,
  ) -> Result<usize, ProofVerifyError> {
    // serialise and add the IPP commitment to the transcript
    let mut bytes = Vec::new();
    self
      .t
      .serialize_with_mode(&mut bytes, Compress::Yes)
      .unwrap();
    transcript.append(b"", &bytes);

    let c: E::ScalarField = transcript.challenge_scalar(b"");

    let mut input_as_sparse_poly_entries = vec![SparsePolyEntry::new(0, E::ScalarField::one())];
    //remaining inputs
    input_as_sparse_poly_entries.extend(
      (0..input.len())
        .map(|i| SparsePolyEntry::new(i + 1, input[i]))
        .collect::<Vec<SparsePolyEntry<E::ScalarField>>>(),
    );

    let n = num_vars;
    let input_as_sparse_poly =
      SparsePolynomial::new(n.log_2() as usize, input_as_sparse_poly_entries);

    let config = VerifierConfig {
      num_vars,
      num_cons,
      input: input.to_vec(),
      evals: *evals,
      params: poseidon,
      prev_challenge: c,
      claims_phase2: self.claims_phase2,
      polys_sc1: self.sc_proof_phase1.polys.clone(),
      polys_sc2: self.sc_proof_phase2.polys.clone(),
      eval_vars_at_ry: self.eval_vars_at_ry,
      input_as_sparse_poly,
      ry: self.ry.clone(),
      comm: self.comm.clone(),
      transcript_sat_state: self.transcript_sat_state,
    };

    let _rng = ark_std::test_rng();
    let circuit = R1CSVerificationCircuit::new(&config);
    let cs = ConstraintSystem::<E::ScalarField>::new_ref();
    circuit.generate_constraints(cs.clone()).unwrap();
    assert!(cs.is_satisfied().unwrap());

    Ok(cs.num_constraints())
  }
}

// fn verify_constraints_outer(circuit: VerifierCircuit, _num_cons: &usize) -> usize {
//   let cs = ConstraintSystem::<Fq>::new_ref();
//   circuit.generate_constraints(cs.clone()).unwrap();
//   assert!(cs.is_satisfied().unwrap());
//   cs.num_constraints()
// }

// fn verify_constraints_inner(circuit: VerifierCircuit, _num_cons: &usize) -> usize {
//   let cs = ConstraintSystem::<Fr>::new_ref();
//   circuit
//     .inner_circuit
//     .generate_constraints(cs.clone())
//     .unwrap();
//   assert!(cs.is_satisfied().unwrap());
//   cs.num_constraints()
// }

#[cfg(test)]
mod tests {
  use crate::parameters::poseidon_params;

  use super::*;
  type F = ark_bls12_377::Fr;
  type E = ark_bls12_377::Bls12_377;

  use ark_std::UniformRand;

  fn produce_tiny_r1cs() -> (R1CSInstance<F>, Vec<F>, Vec<F>) {
    // three constraints over five variables Z1, Z2, Z3, Z4, and Z5
    // rounded to the nearest power of two
    let num_cons = 128;
    let num_vars = 256;
    let num_inputs = 2;

    // encode the above constraints into three matrices
    let mut A: Vec<(usize, usize, F)> = Vec::new();
    let mut B: Vec<(usize, usize, F)> = Vec::new();
    let mut C: Vec<(usize, usize, F)> = Vec::new();

    let one = F::one();
    // constraint 0 entries
    // (Z1 + Z2) * I0 - Z3 = 0;
    A.push((0, 0, one));
    A.push((0, 1, one));
    B.push((0, num_vars + 1, one));
    C.push((0, 2, one));

    // constraint 1 entries
    // (Z1 + I1) * (Z3) - Z4 = 0
    A.push((1, 0, one));
    A.push((1, num_vars + 2, one));
    B.push((1, 2, one));
    C.push((1, 3, one));
    // constraint 3 entries
    // Z5 * 1 - 0 = 0
    A.push((2, 4, one));
    B.push((2, num_vars, one));

    let inst = R1CSInstance::new(num_cons, num_vars, num_inputs, &A, &B, &C);

    // compute a satisfying assignment
    let mut rng = ark_std::rand::thread_rng();
    let i0 = F::rand(&mut rng);
    let i1 = F::rand(&mut rng);
    let z1 = F::rand(&mut rng);
    let z2 = F::rand(&mut rng);
    let z3 = (z1 + z2) * i0; // constraint 1: (Z1 + Z2) * I0 - Z3 = 0;
    let z4 = (z1 + i1) * z3; // constraint 2: (Z1 + I1) * (Z3) - Z4 = 0
    let z5 = F::zero(); //constraint 3

    let mut vars = vec![F::zero(); num_vars];
    vars[0] = z1;
    vars[1] = z2;
    vars[2] = z3;
    vars[3] = z4;
    vars[4] = z5;

    let mut input = vec![F::zero(); num_inputs];
    input[0] = i0;
    input[1] = i1;

    (inst, vars, input)
  }

  #[test]
  fn test_tiny_r1cs() {
    let (inst, vars, input) = tests::produce_tiny_r1cs();
    let is_sat = inst.is_sat(&vars, &input);
    assert!(is_sat);
  }

  #[test]
  fn test_synthetic_r1cs() {
    let (inst, vars, input) = R1CSInstance::<F>::produce_synthetic_r1cs(1024, 1024, 10);
    let is_sat = inst.is_sat(&vars, &input);
    assert!(is_sat);
  }

  #[test]
  pub fn check_r1cs_proof() {
    let num_vars = 16;
    let num_cons = num_vars;
    let num_inputs = 3;
    let (inst, vars, input) =
      R1CSInstance::<F>::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);

    let gens = R1CSGens::<E>::new(b"test-m", num_cons, num_vars);

    let params = poseidon_params();
    // let mut random_tape = RandomTape::new(b"proof");

    let mut prover_transcript = PoseidonTranscript::new(&params);
    let (proof, rx, ry) = R1CSProof::prove(&inst, vars, &input, &gens, &mut prover_transcript);

    let inst_evals = inst.evaluate(&rx, &ry);

    let mut verifier_transcript = PoseidonTranscript::new(&params);

    // if you want to check the test fails
    // input[0] = Scalar::zero();

    assert!(proof
      .verify_groth16(
        inst.get_num_vars(),
        inst.get_num_cons(),
        &input,
        &inst_evals,
        &mut verifier_transcript,
        &gens,
        poseidon_params()
      )
      .is_ok());
  }
}
