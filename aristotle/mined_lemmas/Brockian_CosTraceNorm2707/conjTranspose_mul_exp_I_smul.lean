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

lemma conjTranspose_mul_exp_I_smul {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    (exp (Complex.I • A))ᴴ * exp (Complex.I • A) = 1 := by
  have h1 : (Complex.I • A)ᴴ = -(Complex.I • A) := by
    rw [Matrix.conjTranspose_smul, hA.eq]; simp
  have h2 : (exp (Complex.I • A))ᴴ = exp (-(Complex.I • A)) := by
    rw [← h1, Matrix.exp_conjTranspose]
  rw [h2, Matrix.exp_neg]
  exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _))

/-- For a Hermitian matrix `A`, the matrix `exp (-i A)` is unitary as well. -/
