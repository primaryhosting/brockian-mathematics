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

theorem homogSum_eq_sum (f : ℕ → ℤ) (d n : ℕ) :
    homogSum f d n = ∑ i ∈ Finset.Icc 1 n, f (i * d) := by
  induction n with
  | zero => simp [homogSum]
  | succ k ih =>
      rw [homogSum_succ, ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)]

/-- **Erdős discrepancy, base case `C = 1`, in Mathlib notation.**
For every `±1`-valued sequence `f` there are `d, n ≥ 1` with
`|f d + f (2d) + ⋯ + f (nd)| ≥ 2`. -/
