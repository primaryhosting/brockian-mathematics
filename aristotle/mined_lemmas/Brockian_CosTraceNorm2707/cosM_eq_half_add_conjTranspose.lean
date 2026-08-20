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

lemma cosM_eq_half_add_conjTranspose {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    cosM A = (2 : ℂ)⁻¹ • (exp (Complex.I • A) + (exp (Complex.I • A))ᴴ) := by
  rw [cosM, conjTranspose_exp_I_smul hA]

/-- The matrix cosine of a Hermitian matrix is Hermitian. -/
