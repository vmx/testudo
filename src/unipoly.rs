use crate::poseidon_transcript::{PoseidonTranscript, TranscriptWriter};
use ark_crypto_primitives::sponge::Absorb;
use ark_ff::{Field, PrimeField};
use ark_serialize::*;
// ax^2 + bx + c stored as vec![c,b,a]
// ax^3 + bx^2 + cx + d stored as vec![d,c,b,a]
#[derive(Debug, CanonicalDeserialize, CanonicalSerialize, Clone)]
pub struct UniPoly<F: Field> {
  pub coeffs: Vec<F>,
  // pub coeffs_fq: Vec<Fq>,
}

// ax^2 + bx + c stored as vec![c,a]
// ax^3 + bx^2 + cx + d stored as vec![d,b,a]
#[derive(CanonicalSerialize, CanonicalDeserialize, Debug)]
pub struct CompressedUniPoly<F: Field> {
  pub coeffs_except_linear_term: Vec<F>,
}

impl<F: Field> UniPoly<F> {
  pub fn from_evals(evals: &[F]) -> Self {
    // we only support degree-2 or degree-3 univariate polynomials
    assert!(evals.len() == 3 || evals.len() == 4);
    let coeffs = if evals.len() == 3 {
      // ax^2 + bx + c
      let two_inv = F::from(2 as u8).inverse().unwrap();

      let c = evals[0];
      let a = two_inv * (evals[2] - evals[1] - evals[1] + c);
      let b = evals[1] - c - a;
      vec![c, b, a]
    } else {
      // ax^3 + bx^2 + cx + d
      let two_inv = F::from(2 as u8).inverse().unwrap();
      let six_inv = F::from(6 as u8).inverse().unwrap();

      let d = evals[0];
      let a = six_inv
        * (evals[3] - evals[2] - evals[2] - evals[2] + evals[1] + evals[1] + evals[1] - evals[0]);
      let b = two_inv
        * (evals[0] + evals[0] - evals[1] - evals[1] - evals[1] - evals[1] - evals[1]
          + evals[2]
          + evals[2]
          + evals[2]
          + evals[2]
          - evals[3]);
      let c = evals[1] - d - a - b;
      vec![d, c, b, a]
    };

    UniPoly { coeffs }
  }

  pub fn degree(&self) -> usize {
    self.coeffs.len() - 1
  }

  pub fn eval_at_zero(&self) -> F {
    self.coeffs[0]
  }

  pub fn eval_at_one(&self) -> F {
    (0..self.coeffs.len()).map(|i| self.coeffs[i]).sum()
  }

  pub fn evaluate(&self, r: &F) -> F {
    let mut eval = self.coeffs[0];
    let mut power = *r;
    for i in 1..self.coeffs.len() {
      eval += power * self.coeffs[i];
      power *= r;
    }
    eval
  }
  // pub fn compress(&self) -> CompressedUniPoly<F> {
  //   let coeffs_except_linear_term = [&self.coeffs[..1], &self.coeffs[2..]].concat();
  //   assert_eq!(coeffs_except_linear_term.len() + 1, self.coeffs.len());
  //   CompressedUniPoly {
  //     coeffs_except_linear_term,
  //   }
  // }
}

// impl<F: PrimeField> CompressedUniPoly<F> {
//   // we require eval(0) + eval(1) = hint, so we can solve for the linear term as:
//   // linear_term = hint - 2 * constant_term - deg2 term - deg3 term
//   pub fn decompress(&self, hint: &F) -> UniPoly<F> {
//     let mut linear_term =
//       (*hint) - self.coeffs_except_linear_term[0] - self.coeffs_except_linear_term[0];
//     for i in 1..self.coeffs_except_linear_term.len() {
//       linear_term -= self.coeffs_except_linear_term[i];
//     }

//     let mut coeffs = vec![self.coeffs_except_linear_term[0], linear_term];
//     coeffs.extend(&self.coeffs_except_linear_term[1..]);
//     assert_eq!(self.coeffs_except_linear_term.len() + 1, coeffs.len());
//     UniPoly { coeffs }
//   }
// }

impl<F: PrimeField + Absorb> TranscriptWriter<F> for UniPoly<F> {
  fn write_to_transcript(&self, transcript: &mut PoseidonTranscript<F>) {
    // transcript.append_message(label, b"UniPoly_begin");
    for i in 0..self.coeffs.len() {
      transcript.append_scalar(b"", &self.coeffs[i]);
    }
    // transcript.append_message(label, b"UniPoly_end");
  }
}

#[cfg(test)]
mod tests {

  use ark_ff::One;

  use super::*;

  type F = ark_bls12_377::Fr;

  #[test]
  fn test_from_evals_quad() {
    // polynomial is 2x^2 + 3x + 1
    let e0 = F::one();
    let e1 = F::from(6 as u8);
    let e2 = F::from(15 as u8);
    let evals = vec![e0, e1, e2];
    let poly = UniPoly::from_evals(&evals);

    assert_eq!(poly.eval_at_zero(), e0);
    assert_eq!(poly.eval_at_one(), e1);
    assert_eq!(poly.coeffs.len(), 3);
    assert_eq!(poly.coeffs[0], F::one());
    assert_eq!(poly.coeffs[1], F::from(3 as u8));
    assert_eq!(poly.coeffs[2], F::from(2 as u8));

    // let hint = e0 + e1;
    // // let compressed_poly = poly.compress();
    // // let decompressed_poly = compressed_poly.decompress(&hint);
    // for i in 0..poly.coeffs.len() {
    //   assert_eq!(poly.coeffs[i], poly.coeffs[i]);
    // }

    let e3 = F::from(28 as u8);
    assert_eq!(poly.evaluate(&F::from(3 as u8)), e3);
  }

  #[test]
  fn test_from_evals_cubic() {
    // polynomial is x^3 + 2x^2 + 3x + 1
    let e0 = F::one();
    let e1 = F::from(7);
    let e2 = F::from(23);
    let e3 = F::from(55);
    let evals = vec![e0, e1, e2, e3];
    let poly = UniPoly::from_evals(&evals);

    assert_eq!(poly.eval_at_zero(), e0);
    assert_eq!(poly.eval_at_one(), e1);
    assert_eq!(poly.coeffs.len(), 4);
    assert_eq!(poly.coeffs[0], F::one());
    assert_eq!(poly.coeffs[1], F::from(3));
    assert_eq!(poly.coeffs[2], F::from(2));
    assert_eq!(poly.coeffs[3], F::from(1));

    // let hint = e0 + e1;
    // let compressed_poly = poly.compress();
    // let decompressed_poly = compressed_poly.decompress(&hint);
    // for i in 0..decompressed_poly.coeffs.len() {
    //   assert_eq!(decompressed_poly.coeffs[i], poly.coeffs[i]);
    // }

    let e4 = F::from(109);
    assert_eq!(poly.evaluate(&F::from(4)), e4);
  }
}
