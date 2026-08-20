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

lemma norm_trace_le_of_norm_entries {U : Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ i j, ‖U i j‖ ≤ 1) : ‖U.trace‖ ≤ n := by
  rw [Matrix.trace]
  calc ‖∑ i, U.diag i‖ ≤ ∑ i : Fin n, ‖U.diag i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => h i i
    _ = n := by simp

/-- If `Uᴴ * U = 1` then the trace of `U` has norm at most the size of the matrix. -/
