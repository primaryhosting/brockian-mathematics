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

theorem SinTraceNorm2707 {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    ‖(sinM A).trace‖ ≤ n := by
  have h1 := norm_trace_exp_I_smul_le hA
  have h2 := norm_trace_exp_neg_I_smul_le hA
  rw [trace_sinM, norm_mul]
  have hnorm : ‖(2 * Complex.I)⁻¹‖ = 1 / 2 := by
    rw [norm_inv, norm_mul]; simp
  have hsum : ‖(exp (Complex.I • A)).trace - (exp (-(Complex.I • A))).trace‖ ≤ (n : ℝ) + n :=
    (norm_sub_le _ _).trans (add_le_add h1 h2)
  rw [hnorm]
  nlinarith [norm_nonneg ((exp (Complex.I • A)).trace - (exp (-(Complex.I • A))).trace)]

/-- For Hermitian `A`, the conjugate transpose of `exp (i A)` is `exp (-i A)`. -/
