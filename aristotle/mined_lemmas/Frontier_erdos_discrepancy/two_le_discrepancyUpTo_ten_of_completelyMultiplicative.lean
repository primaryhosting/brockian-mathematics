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

theorem two_le_discrepancyUpTo_ten_of_completelyMultiplicative {f : ℕ → ℤ}
    (hcm : CompletelyMultiplicative f) (hf : IsPMOne f) : 2 ≤ discrepancyUpTo f 10 := by
  obtain ⟨n, hn1, hn2, hlt⟩ := completelyMultiplicative_exists_sum_gt_one hcm hf
  exact le_trans hlt (le_discrepancyUpTo le_rfl hn1 (by simpa using hn2))

/-! ### Sharpness: an explicit completely multiplicative example of discrepancy `1`
up to `9` -/

/-- The completely multiplicative `±1` sequence with `f p = -1` for every prime `p ≠ 7`
and `f 7 = 1`. -/
