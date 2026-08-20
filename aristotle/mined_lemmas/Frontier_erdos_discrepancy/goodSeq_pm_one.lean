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

theorem goodSeq_pm_one : IsPMOne goodSeq := by
  intro n _
  by_cases h : n < 12
  · interval_cases n <;> decide
  · left
    have hlen : goodPattern.length ≤ n := by simp [goodPattern]; omega
    show goodPattern.getD n 1 = 1
    exact List.getD_eq_default _ _ hlen

/-- The explicit sequence has discrepancy at most `1` on every homogeneous arithmetic
progression contained in `{1, …, 11}`. -/
