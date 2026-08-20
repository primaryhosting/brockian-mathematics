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

theorem two_mul_triIdx_add_one (k : ℕ) : 2 * triIdx k + 1 = 3 ^ (k + 1) := by
  induction k with
  | zero => norm_num [triIdx]
  | succ j ih =>
      have : triIdx (j + 1) = 3 * triIdx j + 1 := rfl
      rw [this]
      ring_nf
      ring_nf at ih
      omega

/-- The partial sum at the index `a k` equals `k + 1`. -/
