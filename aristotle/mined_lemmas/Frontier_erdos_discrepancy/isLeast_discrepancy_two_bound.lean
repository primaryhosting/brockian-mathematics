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

theorem isLeast_discrepancy_two_bound :
    IsLeast {N : ℕ | ∀ f : ℕ → ℤ, IsPMOne f → 2 ≤ discrepancyUpTo f N} 12 := by
  constructor
  · intro f hf
    exact two_le_discrepancyUpTo_twelve f hf
  · intro N hN
    by_contra hlt
    have h11 : N ≤ 11 := by omega
    have h1 : 2 ≤ discrepancyUpTo goodSeq N := hN goodSeq goodSeq_pm_one
    have h2 : discrepancyUpTo goodSeq N ≤ 1 := by
      rw [← discrepancyUpTo_goodSeq_eleven]
      exact discrepancyUpTo_mono h11
    omega

/-- The finitary statement, in terms of the discrepancy function: for every bound `C`
there is a length `N` beyond which *every* `±1` sequence exceeds `C`. -/
