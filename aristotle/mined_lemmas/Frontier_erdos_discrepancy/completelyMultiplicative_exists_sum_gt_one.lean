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

theorem completelyMultiplicative_exists_sum_gt_one {f : ℕ → ℤ}
    (hcm : CompletelyMultiplicative f) (hf : IsPMOne f) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ 10 ∧ 1 < (homogSum f 1 n).natAbs := by
  -- the values forced by complete multiplicativity
  have e1 : f 1 = 1 := by
    have h11 : f 1 = f 1 * f 1 := by simpa using hcm 1 1 le_rfl le_rfl
    rcases hf 1 le_rfl with h | h
    · exact h
    · rw [h] at h11; norm_num at h11
  have e4 : f 4 = f 2 * f 2 := by simpa using hcm 2 2 (by norm_num) (by norm_num)
  have e6 : f 6 = f 2 * f 3 := by simpa using hcm 2 3 (by norm_num) (by norm_num)
  have e8 : f 8 = f 2 * (f 2 * f 2) := by
    have : f 8 = f 2 * f 4 := by simpa using hcm 2 4 (by norm_num) (by norm_num)
    rw [this, e4]
  have e9 : f 9 = f 3 * f 3 := by simpa using hcm 3 3 (by norm_num) (by norm_num)
  have e10 : f 10 = f 2 * f 5 := by simpa using hcm 2 5 (by norm_num) (by norm_num)
  -- the partial sums in terms of `f 2, f 3, f 5, f 7`
  have s4 : homogSum f 1 4 = 1 + f 2 + f 3 + f 2 * f 2 := by
    show f 1 + f 2 + f 3 + f 4 = _
    rw [e1, e4]
  have s6 : homogSum f 1 6 = 1 + f 2 + f 3 + f 2 * f 2 + f 5 + f 2 * f 3 := by
    show f 1 + f 2 + f 3 + f 4 + f 5 + f 6 = _
    rw [e1, e4, e6]
  have s8 : homogSum f 1 8 =
      1 + f 2 + f 3 + f 2 * f 2 + f 5 + f 2 * f 3 + f 7 + f 2 * (f 2 * f 2) := by
    show f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 = _
    rw [e1, e4, e6, e8]
  have s10 : homogSum f 1 10 =
      1 + f 2 + f 3 + f 2 * f 2 + f 5 + f 2 * f 3 + f 7 + f 2 * (f 2 * f 2)
        + f 3 * f 3 + f 2 * f 5 := by
    show f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 = _
    rw [e1, e4, e6, e8, e9, e10]
  -- one of the four sums must be large
  by_contra hcon
  push_neg at hcon
  have h4 := hcon 4 (by norm_num) (by norm_num)
  have h6 := hcon 6 (by norm_num) (by norm_num)
  have h8 := hcon 8 (by norm_num) (by norm_num)
  have h10 := hcon 10 (by norm_num) (by norm_num)
  rw [s4] at h4
  rw [s6] at h6
  rw [s8] at h8
  rw [s10] at h10
  have := cm_arith (hf 2 (by norm_num)) (hf 3 (by norm_num)) (hf 5 (by norm_num))
    (hf 7 (by norm_num)) h4 h6 h8
  omega

/-- **Every completely multiplicative `±1` sequence has discrepancy at least `2` already
inside `{1, …, 10}`.** -/
