#![allow(non_snake_case)]
#![doc = include_str!("../README.md")]
#![feature(test)]
#![allow(clippy::assertions_on_result_states)]

extern crate ark_std;
extern crate core;
extern crate digest;
extern crate lazy_static;
extern crate merlin;
extern crate rand;
extern crate sha3;
extern crate test;

#[macro_use]
extern crate json;

#[cfg(feature = "multicore")]
extern crate rayon;

mod commitments;
mod dense_mlpoly;
mod errors;
#[macro_use]
pub(crate) mod macros;
mod math;
pub(crate) mod mipp;
mod nizk;
mod product_tree;
mod r1csinstance;
mod r1csproof;
mod sparse_mlpoly;
mod sqrt_pst;
mod sumcheck;
mod timer;
pub(crate) mod transcript;
mod unipoly;

pub mod parameters;

mod constraints;
pub mod poseidon_transcript;

use ark_crypto_primitives::sponge::poseidon::PoseidonConfig;
use ark_crypto_primitives::sponge::Absorb;
use ark_serialize::*;
use core::cmp::max;
use errors::{ProofVerifyError, R1CSError};
use transcript::Transcript;
use transcript::TranscriptWriter;

use poseidon_transcript::PoseidonTranscript;
use r1csinstance::{
  R1CSCommitment, R1CSCommitmentGens, R1CSDecommitment, R1CSEvalProof, R1CSInstance,
};
use r1csproof::{R1CSGens, R1CSProof};

use ark_ec::CurveGroup;
use timer::Timer;

/// `ComputationCommitment` holds a public preprocessed NP statement (e.g., R1CS)
pub struct ComputationCommitment<G: CurveGroup> {
  comm: R1CSCommitment<G>,
}

use ark_ff::PrimeField;
/// `ComputationDecommitment` holds information to decommit `ComputationCommitment`
pub struct ComputationDecommitment<F: PrimeField> {
  decomm: R1CSDecommitment<F>,
}

/// `Assignment` holds an assignment of values to either the inputs or variables in an `Instance`
#[derive(Clone)]
pub struct Assignment<F: PrimeField> {
  assignment: Vec<F>,
}

impl<F: PrimeField> Assignment<F> {
  /// Constructs a new `Assignment` from a vector
  pub fn new(assignment: &Vec<Vec<u8>>) -> Result<Self, R1CSError> {
    let bytes_to_scalar = |vec: &Vec<Vec<u8>>| -> Result<Vec<F>, R1CSError> {
      let mut vec_scalar: Vec<F> = Vec::new();
      for v in vec {
        let val = F::from_random_bytes(v.as_slice());
        if let Some(v) = val {
          vec_scalar.push(v);
        } else {
          return Err(R1CSError::InvalidScalar);
        }
      }
      Ok(vec_scalar)
    };

    let assignment_scalar = bytes_to_scalar(assignment);

    // check for any parsing errors
    if assignment_scalar.is_err() {
      return Err(R1CSError::InvalidScalar);
    }

    Ok(Assignment {
      assignment: assignment_scalar.unwrap(),
    })
  }

  /// pads Assignment to the specified length
  fn pad(&self, len: usize) -> VarsAssignment<F> {
    // check that the new length is higher than current length
    assert!(len > self.assignment.len());

    let padded_assignment = {
      let mut padded_assignment = self.assignment.clone();
      padded_assignment.extend(vec![F::zero(); len - self.assignment.len()]);
      padded_assignment
    };

    VarsAssignment {
      assignment: padded_assignment,
    }
  }
}

/// `VarsAssignment` holds an assignment of values to variables in an `Instance`
pub type VarsAssignment<F> = Assignment<F>;

/// `InputsAssignment` holds an assignment of values to variables in an `Instance`
pub type InputsAssignment<F> = Assignment<F>;

/// `Instance` holds the description of R1CS matrices and a hash of the matrices
#[derive(Debug)]
pub struct Instance<F: PrimeField> {
  inst: R1CSInstance<F>,
  digest: Vec<u8>,
}

impl<F: PrimeField> Instance<F> {
  /// Constructs a new `Instance` and an associated satisfying assignment
  pub fn new(
    num_cons: usize,
    num_vars: usize,
    num_inputs: usize,
    A: &[(usize, usize, Vec<u8>)],
    B: &[(usize, usize, Vec<u8>)],
    C: &[(usize, usize, Vec<u8>)],
  ) -> Result<Self, R1CSError> {
    let (num_vars_padded, num_cons_padded) = {
      let num_vars_padded = {
        let mut num_vars_padded = num_vars;

        // ensure that num_inputs + 1 <= num_vars
        num_vars_padded = max(num_vars_padded, num_inputs + 1);

        // ensure that num_vars_padded a power of two
        if num_vars_padded.next_power_of_two() != num_vars_padded {
          num_vars_padded = num_vars_padded.next_power_of_two();
        }
        num_vars_padded
      };

      let num_cons_padded = {
        let mut num_cons_padded = num_cons;

        // ensure that num_cons_padded is at least 2
        if num_cons_padded == 0 || num_cons_padded == 1 {
          num_cons_padded = 2;
        }

        // ensure that num_cons_padded is power of 2
        if num_cons.next_power_of_two() != num_cons {
          num_cons_padded = num_cons.next_power_of_two();
        }
        num_cons_padded
      };

      (num_vars_padded, num_cons_padded)
    };

    let bytes_to_scalar =
      |tups: &[(usize, usize, Vec<u8>)]| -> Result<Vec<(usize, usize, F)>, R1CSError> {
        let mut mat: Vec<(usize, usize, F)> = Vec::new();
        for (row, col, val_bytes) in tups {
          // row must be smaller than num_cons
          if *row >= num_cons {
            return Err(R1CSError::InvalidIndex);
          }

          // col must be smaller than num_vars + 1 + num_inputs
          if *col >= num_vars + 1 + num_inputs {
            return Err(R1CSError::InvalidIndex);
          }

          let val = F::from_random_bytes(val_bytes.as_slice());
          if let Some(v) = val {
            // if col >= num_vars, it means that it is referencing a 1 or input in the satisfying
            // assignment
            if *col >= num_vars {
              mat.push((*row, *col + num_vars_padded - num_vars, v));
            } else {
              mat.push((*row, *col, v));
            }
          } else {
            return Err(R1CSError::InvalidScalar);
          }
        }

        // pad with additional constraints up until num_cons_padded if the original constraints were 0 or 1
        // we do not need to pad otherwise because the dummy constraints are implicit in the sum-check protocol
        if num_cons == 0 || num_cons == 1 {
          for i in tups.len()..num_cons_padded {
            mat.push((i, num_vars, F::zero()));
          }
        }

        Ok(mat)
      };

    let A_scalar = bytes_to_scalar(A);
    if A_scalar.is_err() {
      return Err(A_scalar.err().unwrap());
    }

    let B_scalar = bytes_to_scalar(B);
    if B_scalar.is_err() {
      return Err(B_scalar.err().unwrap());
    }

    let C_scalar = bytes_to_scalar(C);
    if C_scalar.is_err() {
      return Err(C_scalar.err().unwrap());
    }

    let inst = R1CSInstance::new(
      num_cons_padded,
      num_vars_padded,
      num_inputs,
      &A_scalar.unwrap(),
      &B_scalar.unwrap(),
      &C_scalar.unwrap(),
    );

    let digest = inst.get_digest();

    Ok(Instance { inst, digest })
  }

  /// Checks if a given R1CSInstance is satisfiable with a given variables and inputs assignments
  pub fn is_sat(
    &self,
    vars: &VarsAssignment<F>,
    inputs: &InputsAssignment<F>,
  ) -> Result<bool, R1CSError> {
    if vars.assignment.len() > self.inst.get_num_vars() {
      return Err(R1CSError::InvalidNumberOfInputs);
    }

    if inputs.assignment.len() != self.inst.get_num_inputs() {
      return Err(R1CSError::InvalidNumberOfInputs);
    }

    // we might need to pad variables
    let padded_vars = {
      let num_padded_vars = self.inst.get_num_vars();
      let num_vars = vars.assignment.len();
      if num_padded_vars > num_vars {
        vars.pad(num_padded_vars)
      } else {
        vars.clone()
      }
    };

    Ok(
      self
        .inst
        .is_sat(&padded_vars.assignment, &inputs.assignment),
    )
  }

  /// Constructs a new synthetic R1CS `Instance` and an associated satisfying assignment
  pub fn produce_synthetic_r1cs(
    num_cons: usize,
    num_vars: usize,
    num_inputs: usize,
  ) -> (Instance<F>, VarsAssignment<F>, InputsAssignment<F>) {
    let (inst, vars, inputs) = R1CSInstance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);
    let digest = inst.get_digest();
    (
      Instance { inst, digest },
      VarsAssignment { assignment: vars },
      InputsAssignment { assignment: inputs },
    )
  }
}

/// `SNARKGens` holds public parameters for producing and verifying proofs with the Spartan SNARK
pub struct SNARKGens<E: Pairing> {
  gens_r1cs_sat: R1CSGens<E>,
  gens_r1cs_eval: R1CSCommitmentGens<E>,
}

impl<E: Pairing> SNARKGens<E> {
  /// Constructs a new `SNARKGens` given the size of the R1CS statement
  /// `num_nz_entries` specifies the maximum number of non-zero entries in any of the three R1CS matrices
  pub fn new(num_cons: usize, num_vars: usize, num_inputs: usize, num_nz_entries: usize) -> Self {
    let num_vars_padded = {
      let mut num_vars_padded = max(num_vars, num_inputs + 1);
      if num_vars_padded != num_vars_padded.next_power_of_two() {
        num_vars_padded = num_vars_padded.next_power_of_two();
      }
      num_vars_padded
    };

    let gens_r1cs_sat = R1CSGens::new(b"gens_r1cs_sat", num_cons, num_vars_padded);
    let gens_r1cs_eval = R1CSCommitmentGens::new(
      b"gens_r1cs_eval",
      num_cons,
      num_vars_padded,
      num_inputs,
      num_nz_entries,
    );
    SNARKGens {
      gens_r1cs_sat,
      gens_r1cs_eval,
    }
  }
}

use ark_ec::pairing::Pairing;
/// `SNARK` holds a proof produced by Spartan SNARK
#[derive(CanonicalSerialize, CanonicalDeserialize, Debug)]
pub struct SNARK<E: Pairing> {
  r1cs_sat_proof: R1CSProof<E>,
  inst_evals: (E::ScalarField, E::ScalarField, E::ScalarField),
  r1cs_eval_proof: R1CSEvalProof<E>,
  rx: Vec<E::ScalarField>,
  ry: Vec<E::ScalarField>,
}

impl<E> SNARK<E>
where
  E: Pairing,
  E::ScalarField: Absorb,
{
  /// A public computation to create a commitment to an R1CS instance
  pub fn encode(
    inst: &Instance<E::ScalarField>,
    gens: &SNARKGens<E>,
  ) -> (
    ComputationCommitment<E::G1>,
    ComputationDecommitment<E::ScalarField>,
  ) {
    let timer_encode = Timer::new("SNARK::encode");
    let (comm, decomm) = inst.inst.commit(&gens.gens_r1cs_eval);
    timer_encode.stop();
    (
      ComputationCommitment { comm },
      ComputationDecommitment { decomm },
    )
  }

  /// A method to produce a SNARK proof of the satisfiability of an R1CS instance
  pub fn prove(
    inst: &Instance<E::ScalarField>,
    comm: &ComputationCommitment<E::G1>,
    decomm: &ComputationDecommitment<E::ScalarField>,
    vars: VarsAssignment<E::ScalarField>,
    inputs: &InputsAssignment<E::ScalarField>,
    gens: &SNARKGens<E>,
    transcript: &mut PoseidonTranscript<E::ScalarField>,
  ) -> Self {
    let timer_prove = Timer::new("SNARK::prove");

    // transcript.append_protocol_name(SNARK::protocol_name());
    comm.comm.write_to_transcript(transcript);

    let (r1cs_sat_proof, rx, ry) = {
      let (proof, rx, ry) = {
        // we might need to pad variables
        let padded_vars = {
          let num_padded_vars = inst.inst.get_num_vars();
          let num_vars = vars.assignment.len();
          if num_padded_vars > num_vars {
            vars.pad(num_padded_vars)
          } else {
            vars
          }
        };

        R1CSProof::prove(
          &inst.inst,
          padded_vars.assignment,
          &inputs.assignment,
          &gens.gens_r1cs_sat,
          transcript,
        )
      };

      let mut proof_encoded: Vec<u8> = Vec::new();
      proof
        .serialize_with_mode(&mut proof_encoded, Compress::Yes)
        .unwrap();
      Timer::print(&format!("len_r1cs_sat_proof {:?}", proof_encoded.len()));

      (proof, rx, ry)
    };

    // We need to reset the transcript state before starting the evaluation
    // proof and share this state with the verifier because, on the verifier's
    // side all the previous updates are done on the transcript
    // circuit variable and the transcript outside the circuit will be
    // inconsistent wrt to the prover's.
    // transcript.new_from_state(&r1cs_sat_proof.transcript_sat_state);

    // We send evaluations of A, B, C at r = (rx, ry) as claims
    // to enable the verifier complete the first sum-check
    let timer_eval = Timer::new("eval_sparse_polys");
    let inst_evals = {
      let (Ar, Br, Cr) = inst.inst.evaluate(&rx, &ry);
      transcript.append_scalar(b"", &Ar);
      transcript.append_scalar(b"", &Br);
      transcript.append_scalar(b"", &Cr);
      (Ar, Br, Cr)
    };
    timer_eval.stop();

    let r1cs_eval_proof = {
      let proof = R1CSEvalProof::prove(
        &decomm.decomm,
        &rx,
        &ry,
        &inst_evals,
        &gens.gens_r1cs_eval,
        transcript,
      );

      let mut proof_encoded: Vec<u8> = Vec::new();
      proof
        .serialize_with_mode(&mut proof_encoded, Compress::Yes)
        .unwrap();
      Timer::print(&format!("len_r1cs_eval_proof {:?}", proof_encoded.len()));
      proof
    };

    timer_prove.stop();
    SNARK {
      r1cs_sat_proof,
      inst_evals,
      r1cs_eval_proof,
      rx,
      ry,
    }
  }

  /// A method to verify the SNARK proof of the satisfiability of an R1CS instance
  pub fn verify(
    &self,
    comm: &ComputationCommitment<E::G1>,
    input: &InputsAssignment<E::ScalarField>,
    transcript: &mut PoseidonTranscript<E::ScalarField>,
    gens: &SNARKGens<E>,
    poseidon: PoseidonConfig<E::ScalarField>,
  ) -> Result<(u128, u128, u128), ProofVerifyError> {
    let timer_verify = Timer::new("SNARK::verify");
    // transcript.append_protocol_name(SNARK::protocol_name());

    // append a commitment to the computation to the transcript
    comm.comm.write_to_transcript(transcript);

    let timer_sat_proof = Timer::new("verify_sat_proof");
    assert_eq!(input.assignment.len(), comm.comm.get_num_inputs());
    // let (rx, ry) =
    let res = self.r1cs_sat_proof.verify_groth16(
      comm.comm.get_num_vars(),
      comm.comm.get_num_cons(),
      &input.assignment,
      &self.inst_evals,
      transcript,
      &gens.gens_r1cs_sat,
      poseidon,
    )?;
    timer_sat_proof.stop();

    let timer_eval_proof = Timer::new("verify_eval_proof");
    // Reset the transcript using the state sent by the prover.
    // TODO: find a way to retrieve this state from the circuit. Currently
    // the API for generating constraints doesn't support returning values
    // computed inside the circuit.
    // transcript.new_from_state(&self.r1cs_sat_proof.transcript_sat_state);

    let (Ar, Br, Cr) = &self.inst_evals;
    transcript.append_scalar(b"", Ar);
    transcript.append_scalar(b"", Br);
    transcript.append_scalar(b"", Cr);

    self.r1cs_eval_proof.verify(
      &comm.comm,
      &self.rx,
      &self.ry,
      &self.inst_evals,
      &gens.gens_r1cs_eval,
      transcript,
    )?;
    timer_eval_proof.stop();
    timer_verify.stop();
    Ok(res)
  }
}

#[derive(Clone)]
/// `NIZKGens` holds public parameters for producing and verifying proofs with the Spartan NIZK
pub struct NIZKGens<E: Pairing> {
  gens_r1cs_sat: R1CSGens<E>,
}

impl<E: Pairing> NIZKGens<E> {
  /// Constructs a new `NIZKGens` given the size of the R1CS statement
  pub fn new(num_cons: usize, num_vars: usize, num_inputs: usize) -> Self {
    let num_vars_padded = {
      let mut num_vars_padded = max(num_vars, num_inputs + 1);
      if num_vars_padded != num_vars_padded.next_power_of_two() {
        num_vars_padded = num_vars_padded.next_power_of_two();
      }
      num_vars_padded
    };

    let gens_r1cs_sat = R1CSGens::new(b"gens_r1cs_sat", num_cons, num_vars_padded);
    NIZKGens { gens_r1cs_sat }
  }
}

/// `NIZK` holds a proof produced by Spartan NIZK
#[derive(CanonicalSerialize, CanonicalDeserialize, Debug)]
pub struct NIZK<E: Pairing> {
  r1cs_sat_proof: R1CSProof<E>,
  r: (Vec<E::ScalarField>, Vec<E::ScalarField>),
}

impl<E> NIZK<E>
where
  E: Pairing,
  E::ScalarField: Absorb,
{
  /// A method to produce a NIZK proof of the satisfiability of an R1CS instance
  pub fn prove(
    inst: &Instance<E::ScalarField>,
    vars: VarsAssignment<E::ScalarField>,
    input: &InputsAssignment<E::ScalarField>,
    gens: &NIZKGens<E>,
    transcript: &mut PoseidonTranscript<E::ScalarField>,
  ) -> Self {
    let timer_prove = Timer::new("NIZK::prove");
    // transcript.append_protocol_name(NIZK::protocol_name());
    transcript.append_bytes(b"", &inst.digest);

    let (r1cs_sat_proof, rx, ry) = {
      // we might need to pad variables
      let padded_vars = {
        let num_padded_vars = inst.inst.get_num_vars();
        let num_vars = vars.assignment.len();
        if num_padded_vars > num_vars {
          vars.pad(num_padded_vars)
        } else {
          vars
        }
      };

      let (proof, rx, ry) = R1CSProof::prove(
        &inst.inst,
        padded_vars.assignment,
        &input.assignment,
        &gens.gens_r1cs_sat,
        transcript,
      );
      let mut proof_encoded = Vec::new();
      proof
        .serialize_with_mode(&mut proof_encoded, Compress::Yes)
        .unwrap();
      Timer::print(&format!("len_r1cs_sat_proof {:?}", proof_encoded.len()));
      (proof, rx, ry)
    };

    timer_prove.stop();
    NIZK {
      r1cs_sat_proof,
      r: (rx, ry),
    }
  }

  /// A method to verify a NIZK proof of the satisfiability of an R1CS instance
  pub fn verify(
    &self,
    inst: &Instance<E::ScalarField>,
    input: &InputsAssignment<E::ScalarField>,
    transcript: &mut PoseidonTranscript<E::ScalarField>,
    gens: &NIZKGens<E>,
    poseidon: PoseidonConfig<E::ScalarField>,
  ) -> Result<usize, ProofVerifyError> {
    let timer_verify = Timer::new("NIZK::verify");

    transcript.append_bytes(b"", &inst.digest);

    // We send evaluations of A, B, C at r = (rx, ry) as claims
    // to enable the verifier complete the first sum-check
    // let timer_eval = Timer::new("eval_sparse_polys");
    let (claimed_rx, claimed_ry) = &self.r;
    let inst_evals = inst.inst.evaluate(claimed_rx, claimed_ry);
    // timer_eval.stop();

    let timer_sat_proof = Timer::new("verify_sat_proof");
    assert_eq!(input.assignment.len(), inst.inst.get_num_inputs());
    // let (rx, ry) =
    let nc = self.r1cs_sat_proof.circuit_size(
      inst.inst.get_num_vars(),
      inst.inst.get_num_cons(),
      &input.assignment,
      &inst_evals,
      transcript,
      &gens.gens_r1cs_sat,
      poseidon,
    )?;

    // verify if claimed rx and ry are correct
    // assert_eq!(rx, *claimed_rx);
    // assert_eq!(ry, *claimed_ry);
    timer_sat_proof.stop();
    timer_verify.stop();

    Ok(nc)
  }

  /// A method to verify a NIZK proof of the satisfiability of an R1CS instance with Groth16
  pub fn verify_groth16(
    &self,
    inst: &Instance<E::ScalarField>,
    input: &InputsAssignment<E::ScalarField>,
    transcript: &mut PoseidonTranscript<E::ScalarField>,
    gens: &NIZKGens<E>,
    poseidon: PoseidonConfig<E::ScalarField>,
  ) -> Result<(u128, u128, u128), ProofVerifyError> {
    let timer_verify = Timer::new("NIZK::verify");

    // transcript.append_protocol_name(NIZK::protocol_name());
    transcript.append_bytes(b"", &inst.digest);

    // We send evaluations of A, B, C at r = (rx, ry) as claims
    // to enable the verifier complete the first sum-check
    let timer_eval = Timer::new("eval_sparse_polys");
    let (claimed_rx, claimed_ry) = &self.r;
    let inst_evals = inst.inst.evaluate(claimed_rx, claimed_ry);
    timer_eval.stop();

    let timer_sat_proof = Timer::new("verify_sat_proof");
    assert_eq!(input.assignment.len(), inst.inst.get_num_inputs());
    // let (rx, ry) =
    let (ds, dp, dv) = self.r1cs_sat_proof.verify_groth16(
      inst.inst.get_num_vars(),
      inst.inst.get_num_cons(),
      &input.assignment,
      &inst_evals,
      transcript,
      &gens.gens_r1cs_sat,
      poseidon,
    )?;

    // verify if claimed rx and ry are correct
    // assert_eq!(rx, *claimed_rx);
    // assert_eq!(ry, *claimed_ry);
    timer_sat_proof.stop();
    timer_verify.stop();

    Ok((ds, dp, dv))
  }
}

#[inline]
pub(crate) fn dot_product<F: PrimeField>(a: &[F], b: &[F]) -> F {
  let mut res = F::zero();
  for i in 0..a.len() {
    res += a[i] * &b[i];
  }
  res
}

#[cfg(test)]
mod tests {
  use crate::parameters::poseidon_params;

  use super::*;
  use crate::ark_std::Zero;
  use ark_ff::{BigInteger, One, PrimeField};
  type F = ark_bls12_377::Fr;
  type E = ark_bls12_377::Bls12_377;

  #[test]
  pub fn check_snark() {
    let num_vars = 256;
    let num_cons = num_vars;
    let num_inputs = 10;

    // produce public generators
    let gens = SNARKGens::<E>::new(num_cons, num_vars, num_inputs, num_cons);

    // produce a synthetic R1CSInstance
    let (inst, vars, inputs) = Instance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);

    // create a commitment to R1CSInstance
    let (comm, decomm) = SNARK::encode(&inst, &gens);

    let params = poseidon_params();

    // produce a proof
    let mut prover_transcript = PoseidonTranscript::new(&params);
    let proof = SNARK::prove(
      &inst,
      &comm,
      &decomm,
      vars,
      &inputs,
      &gens,
      &mut prover_transcript,
    );

    // verify the proof
    let mut verifier_transcript = PoseidonTranscript::new(&params);
    assert!(proof
      .verify(
        &comm,
        &inputs,
        &mut verifier_transcript,
        &gens,
        poseidon_params()
      )
      .is_ok());
  }

  #[test]
  pub fn check_r1cs_invalid_index() {
    let num_cons = 4;
    let num_vars = 8;
    let num_inputs = 1;

    let zero: [u8; 32] = [
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0,
    ];

    let A = vec![(0, 0, zero.to_vec())];
    let B = vec![(100, 1, zero.to_vec())];
    let C = vec![(1, 1, zero.to_vec())];

    let inst = Instance::<F>::new(num_cons, num_vars, num_inputs, &A, &B, &C);
    assert!(inst.is_err());
    assert_eq!(inst.err(), Some(R1CSError::InvalidIndex));
  }

  #[test]
  pub fn check_r1cs_invalid_scalar() {
    let num_cons = 4;
    let num_vars = 8;
    let num_inputs = 1;

    let zero: [u8; 32] = [
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0,
    ];

    let larger_than_mod = [
      3, 0, 0, 0, 255, 255, 255, 255, 254, 91, 254, 255, 2, 164, 189, 83, 5, 216, 161, 9, 8, 216,
      57, 51, 72, 125, 157, 41, 83, 167, 237, 115,
    ];

    let A = vec![(0, 0, zero.to_vec())];
    let B = vec![(1, 1, larger_than_mod.to_vec())];
    let C = vec![(1, 1, zero.to_vec())];

    let inst = Instance::<F>::new(num_cons, num_vars, num_inputs, &A, &B, &C);
    assert!(inst.is_err());
    assert_eq!(inst.err(), Some(R1CSError::InvalidScalar));
  }

  #[test]
  fn test_padded_constraints() {
    // parameters of the R1CS instance
    let num_cons = 1;
    let num_vars = 0;
    let num_inputs = 3;
    let num_non_zero_entries = 3;

    // We will encode the above constraints into three matrices, where
    // the coefficients in the matrix are in the little-endian byte order
    let mut A: Vec<(usize, usize, Vec<u8>)> = Vec::new();
    let mut B: Vec<(usize, usize, Vec<u8>)> = Vec::new();
    let mut C: Vec<(usize, usize, Vec<u8>)> = Vec::new();

    // Create a^2 + b + 13
    A.push((0, num_vars + 2, (F::one().into_bigint().to_bytes_le()))); // 1*a
    B.push((0, num_vars + 2, F::one().into_bigint().to_bytes_le())); // 1*a
    C.push((0, num_vars + 1, F::one().into_bigint().to_bytes_le())); // 1*z
    C.push((0, num_vars, (-F::from(13u64)).into_bigint().to_bytes_le())); // -13*1
    C.push((0, num_vars + 3, (-F::one()).into_bigint().to_bytes_le())); // -1*b

    // Var Assignments (Z_0 = 16 is the only output)
    let vars = vec![F::zero().into_bigint().to_bytes_le(); num_vars];

    // create an InputsAssignment (a = 1, b = 2)
    let mut inputs = vec![F::zero().into_bigint().to_bytes_le(); num_inputs];
    inputs[0] = F::from(16u64).into_bigint().to_bytes_le();
    inputs[1] = F::from(1u64).into_bigint().to_bytes_le();
    inputs[2] = F::from(2u64).into_bigint().to_bytes_le();

    let assignment_inputs = InputsAssignment::<F>::new(&inputs).unwrap();
    let assignment_vars = VarsAssignment::new(&vars).unwrap();

    // Check if instance is satisfiable
    let inst = Instance::new(num_cons, num_vars, num_inputs, &A, &B, &C).unwrap();
    let res = inst.is_sat(&assignment_vars, &assignment_inputs);
    assert!(res.unwrap(), "should be satisfied");

    // SNARK public params
    let gens = SNARKGens::<E>::new(num_cons, num_vars, num_inputs, num_non_zero_entries);

    // create a commitment to the R1CS instance
    let (comm, decomm) = SNARK::encode(&inst, &gens);

    let params = poseidon_params();

    // produce a SNARK
    let mut prover_transcript = PoseidonTranscript::new(&params);
    let proof = SNARK::prove(
      &inst,
      &comm,
      &decomm,
      assignment_vars.clone(),
      &assignment_inputs,
      &gens,
      &mut prover_transcript,
    );

    // verify the SNARK
    let mut verifier_transcript = PoseidonTranscript::new(&params);
    assert!(proof
      .verify(
        &comm,
        &assignment_inputs,
        &mut verifier_transcript,
        &gens,
        poseidon_params()
      )
      .is_ok());

    // NIZK public params
    let gens = NIZKGens::<E>::new(num_cons, num_vars, num_inputs);

    let params = poseidon_params();

    // produce a NIZK
    let mut prover_transcript = PoseidonTranscript::new(&params);
    let proof = NIZK::prove(
      &inst,
      assignment_vars,
      &assignment_inputs,
      &gens,
      &mut prover_transcript,
    );

    // verify the NIZK
    let mut verifier_transcript = PoseidonTranscript::new(&params);
    assert!(proof
      .verify_groth16(
        &inst,
        &assignment_inputs,
        &mut verifier_transcript,
        &gens,
        poseidon_params()
      )
      .is_ok());
  }
}
