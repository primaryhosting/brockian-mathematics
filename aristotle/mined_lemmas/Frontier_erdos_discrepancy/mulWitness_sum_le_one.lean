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

theorem mulWitness_sum_le_one {n : ℕ} (hn : 1 ≤ n) (h9 : n ≤ 9) :
    (homogSum mulWitness 1 n).natAbs ≤ 1 := by
  have v1 : mulWitness 1 = 1 := mulWitness_one
  have v2 : mulWitness 2 = -1 := mulWitness_two
  have v3 : mulWitness 3 = -1 := mulWitness_three
  have v5 : mulWitness 5 = -1 := mulWitness_five
  have v7 : mulWitness 7 = 1 := mulWitness_seven
  have v4 : mulWitness 4 = 1 := by
    have := mulWitness_completelyMultiplicative 2 2 (by norm_num) (by norm_num)
    rw [v2] at this; simpa using this
  have v6 : mulWitness 6 = 1 := by
    have := mulWitness_completelyMultiplicative 2 3 (by norm_num) (by norm_num)
    rw [v2, v3] at this; simpa using this
  have v8 : mulWitness 8 = -1 := by
    have := mulWitness_completelyMultiplicative 2 4 (by norm_num) (by norm_num)
    rw [v2, v4] at this; simpa using this
  have v9 : mulWitness 9 = 1 := by
    have := mulWitness_completelyMultiplicative 3 3 (by norm_num) (by norm_num)
    rw [v3] at this; simpa using this
  have s1 : (homogSum mulWitness 1 1).natAbs ≤ 1 := by
    show (mulWitness 1).natAbs ≤ 1
    rw [v1]; decide
  have s2 : (homogSum mulWitness 1 2).natAbs ≤ 1 := by
    show (mulWitness 1 + mulWitness 2).natAbs ≤ 1
    rw [v1, v2]; decide
  have s3 : (homogSum mulWitness 1 3).natAbs ≤ 1 := by
    show (mulWitness 1 + mulWitness 2 + mulWitness 3).natAbs ≤ 1
    rw [v1, v2, v3]; decide
  have s4 : (homogSum mulWitness 1 4).natAbs ≤ 1 := by
    show (mulWitness 1 + mulWitness 2 + mulWitness 3 + mulWitness 4).natAbs ≤ 1
    rw [v1, v2, v3, v4]; decide
  have s5 : (homogSum mulWitness 1 5).natAbs ≤ 1 := by
    show (mulWitness 1 + mulWitness 2 + mulWitness 3 + mulWitness 4 + mulWitness 5).natAbs ≤ 1
    rw [v1, v2, v3, v4, v5]; decide
  have s6 : (homogSum mulWitness 1 6).natAbs ≤ 1 := by
    show (mulWitness 1 + mulWitness 2 + mulWitness 3 + mulWitness 4 + mulWitness 5
      + mulWitness 6).natAbs ≤ 1
    rw [v1, v2, v3, v4, v5, v6]; decide
  have s7 : (homogSum mulWitness 1 7).natAbs ≤ 1 := by
    show (mulWitness 1 + mulWitness 2 + mulWitness 3 + mulWitness 4 + mulWitness 5
      + mulWitness 6 + mulWitness 7).natAbs ≤ 1
    rw [v1, v2, v3, v4, v5, v6, v7]; decide
  have s8 : (homogSum mulWitness 1 8).natAbs ≤ 1 := by
    show (mulWitness 1 + mulWitness 2 + mulWitness 3 + mulWitness 4 + mulWitness 5
      + mulWitness 6 + mulWitness 7 + mulWitness 8).natAbs ≤ 1
    rw [v1, v2, v3, v4, v5, v6, v7, v8]; decide
  have s9 : (homogSum mulWitness 1 9).natAbs ≤ 1 := by
    show (mulWitness 1 + mulWitness 2 + mulWitness 3 + mulWitness 4 + mulWitness 5
      + mulWitness 6 + mulWitness 7 + mulWitness 8 + mulWitness 9).natAbs ≤ 1
    rw [v1, v2, v3, v4, v5, v6, v7, v8, v9]; decide
  interval_cases n <;> assumption

/-- `mulWitness` has discrepancy `1` inside `{1, …, 9}`. -/
