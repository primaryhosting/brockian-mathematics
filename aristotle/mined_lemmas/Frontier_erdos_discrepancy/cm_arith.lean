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

private theorem cm_arith {a b c d : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    (hc : c = 1 ∨ c = -1) (hd : d = 1 ∨ d = -1)
    (h4 : (1 + a + b + a * a).natAbs ≤ 1)
    (h6 : (1 + a + b + a * a + c + a * b).natAbs ≤ 1)
    (h8 : (1 + a + b + a * a + c + a * b + d + a * (a * a)).natAbs ≤ 1) :
    1 < (1 + a + b + a * a + c + a * b + d + a * (a * a) + b * b + a * c).natAbs := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    rcases hd with rfl | rfl <;> norm_num at *

/-- **Base case for completely multiplicative sequences.**  Every completely
multiplicative `±1` sequence has an ordinary partial sum of absolute value at least `2`
among the first ten. -/
