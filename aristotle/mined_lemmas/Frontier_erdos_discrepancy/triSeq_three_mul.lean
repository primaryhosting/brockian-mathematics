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

theorem triSeq_three_mul (m : ℕ) : triSeq (3 * m) = triSeq m := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; norm_num
  · rw [triSeq]
    have h0 : 3 * m % 3 = 0 := by omega
    have h1 : 3 * m ≠ 0 := by omega
    have h2 : 3 * m / 3 = m := by omega
    simp [h0, h1, h2]

