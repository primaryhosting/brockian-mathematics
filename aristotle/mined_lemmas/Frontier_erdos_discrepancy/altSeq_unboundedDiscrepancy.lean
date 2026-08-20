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

theorem altSeq_unboundedDiscrepancy : UnboundedDiscrepancy altSeq := by
  refine unboundedDiscrepancy_of_periodic (p := 2) (by norm_num) (fun n => ?_) altSeq_pm_one
  have h : (n + 2) % 2 = n % 2 := by omega
  simp [altSeq, h]

/-! ### Dilations -/

/-- Dilating a sequence by `k` turns the difference `d` into the difference `k * d`. -/
