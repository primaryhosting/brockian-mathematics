import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Matrix

open NormedSpace (exp)

/-!
# Trace-norm bounds for matrix trigonometric functions

For an `n × n` complex matrix `A` we define the matrix cosine and matrix sine through the
matrix exponential,
`cos A = (exp (i A) + exp (-i A)) / 2` and `sin A = (exp (i A) - exp (-i A)) / (2 i)`.

The main results (`CosTraceNorm2707` and friends) bound the absolute value of the trace of these
matrices by the size `n` of the matrix, whenever `A` is Hermitian.  The proof goes through the
observation that `exp (± i A)` is unitary for Hermitian `A`, so that all of its entries have
absolute value at most `1`.
-/

namespace Brockian

variable {n : ℕ}

/-- The matrix cosine of a square complex matrix, defined through the matrix exponential by
`cos A = (exp (i A) + exp (-i A)) / 2`. -/

lemma isHermitian_sinM {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    (sinM A).IsHermitian := by
  rw [Matrix.IsHermitian, sinM, ← conjTranspose_exp_I_smul hA, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
  rw [show star ((2 * Complex.I)⁻¹) = -(2 * Complex.I)⁻¹ by simp [mul_comm]]
  rw [neg_smul, ← smul_neg, neg_sub]

/-- The trace of the matrix cosine of a Hermitian matrix is real. -/
