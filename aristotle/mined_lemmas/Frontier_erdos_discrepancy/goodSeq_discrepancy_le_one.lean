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

theorem goodSeq_discrepancy_le_one (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (h : n * d ≤ 11) :
    (homogSum goodSeq d n).natAbs ≤ 1 := by
  have hd' : d ≤ 11 := le_trans (Nat.le_mul_of_pos_left d hn) h
  have hn' : n ≤ 11 := le_trans (Nat.le_mul_of_pos_right n hd) h
  interval_cases d <;> interval_cases n <;> first | omega | decide

/-- **Sharpness of the base case.** There is a `±1` sequence all of whose homogeneous
partial sums lying inside `{1, …, 11}` are bounded by `1`; so the twelve values used in
`Frontier.erdos_discrepancy` cannot be reduced to eleven. -/
