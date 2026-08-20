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

theorem CosTraceNorm2707_re {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    -(n : ℝ) ≤ (cosM A).trace.re ∧ (cosM A).trace.re ≤ n := by
  have h := CosTraceNorm2707 hA
  have h1 : |(cosM A).trace.re| ≤ ‖(cosM A).trace‖ := Complex.abs_re_le_norm _
  constructor <;> [linarith [abs_le.mp (h1.trans h) |>.1]; linarith [abs_le.mp (h1.trans h) |>.2]]

/-- **Two-sided trace bound for the matrix sine.** -/
