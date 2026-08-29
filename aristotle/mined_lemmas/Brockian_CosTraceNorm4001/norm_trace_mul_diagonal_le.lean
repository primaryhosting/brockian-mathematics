import Mathlib

/-!
# Cos Trace Norm 4001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm4001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Finset

namespace Brockian

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Unfolding of the unitary conjugation star-algebra automorphism used by the matrix
spectral theorem. -/

theorem norm_trace_mul_diagonal_le {W : Matrix n n ℂ} (hW : W ∈ Matrix.unitaryGroup n ℂ)
    (d : n → ℂ) : ‖(W * diagonal d).trace‖ ≤ ∑ i, ‖d i‖ := by
  rw [Matrix.trace]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
  rw [Matrix.diag_apply, Matrix.mul_diagonal, norm_mul]
  have h := entry_norm_bound_of_unitary hW i i
  nlinarith [norm_nonneg (d i), norm_nonneg (W i i)]

/-- Testing a unitarily-diagonalized matrix against an arbitrary unitary: conjugating moves the
test unitary onto the diagonal factor. -/
