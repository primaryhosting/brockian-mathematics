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

theorem two_le_discrepancyUpTo {f : ℕ → ℤ} (hf : IsPMOne f) {N : ℕ} (h : 12 ≤ N) :
    2 ≤ discrepancyUpTo f N :=
  le_trans (two_le_discrepancyUpTo_twelve f hf) (discrepancyUpTo_mono h)

/-- **The exact threshold for the base case.**  `12` is the least `N` such that *every*
`±1` sequence has discrepancy at least `2` inside `{1, …, N}`: it works, and it fails for
every smaller `N` because of the explicit sequence `goodSeq`. -/
