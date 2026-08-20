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

theorem unboundedDiscrepancy_of_eventuallyEq {f g : ℕ → ℤ} (hf : IsPMOne f) (hg : IsPMOne g)
    {M : ℕ} (h : ∀ k, M ≤ k → f k = g k) (hU : UnboundedDiscrepancy f) :
    UnboundedDiscrepancy g := by
  intro C
  obtain ⟨d, n, hd, hn, hlt⟩ := hU (C + 2 * M)
  refine ⟨d, n, hd, hn, ?_⟩
  have hdiff := homogSum_sub_natAbs_le hf hg hd h n
  have hmin : 2 * min n M ≤ 2 * M := by omega
  omega

end Frontier

import Mathlib
import RequestProject.ErdosDiscrepancy

/-!
# Sharpness of the base case

`Frontier.erdos_discrepancy` shows that every `±1` sequence has discrepancy at least `2`
along some homogeneous arithmetic progression, using only the twelve values `f 1, …, f 12`.
Here we show that twelve values are really needed: there is an explicit `±1` sequence whose
homogeneous partial sums are all bounded by `1` in absolute value as long as they stay
inside `{1, …, 11}`.
-/

namespace Frontier

/-- The pattern `goodPattern[k]` is the `k`-th term (`1 ≤ k ≤ 11`) of a `±1` sequence of
discrepancy `1` on `{1, …, 11}`; entry `0` is a dummy. -/
