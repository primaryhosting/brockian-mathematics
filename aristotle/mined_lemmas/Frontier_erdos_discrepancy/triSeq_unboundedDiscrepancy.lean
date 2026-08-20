import Mathlib
import RequestProject.ErdosDiscrepancy
import RequestProject.ErdosDiscrepancyMathlib
import RequestProject.ErdosDiscrepancySpecialCases
import RequestProject.ErdosDiscrepancyMeasure

/-!
# The base case for completely multiplicative sequences

For a completely multiplicative `±1` sequence every homogeneous sum is `f d` times an
ordinary partial sum, so only the sums `S n = f 1 + ⋯ + f n` matter.  Tracking the four
values `f 2, f 3, f 5, f 7` shows that one of `S 4, S 6, S 8, S 10` must exceed `1` in
absolute value: for completely multiplicative sequences the length `10` already forces
discrepancy `2` (as opposed to `12` in general).
-/

namespace Frontier

/-- Unfolding the ordinary partial sums. -/

theorem triSeq_unboundedDiscrepancy : UnboundedDiscrepancy triSeq := by
  intro C
  refine ⟨1, triIdx C, le_rfl, triIdx_pos C, ?_⟩
  have h : homogSum triSeq 1 (triIdx C) = (C : ℤ) + 1 := triSum_triIdx C
  rw [h]
  omega

/-! ### The sequence is completely multiplicative -/

