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

theorem homogSum_eventually_constant {f : ℕ → ℤ} {d M : ℕ} {c : ℤ}
    (hconst : ∀ i, M ≤ i → 1 ≤ i → f (i * d) = c) :
    ∀ k : ℕ, homogSum f d (M + k) = homogSum f d M + k * c := by
  intro k
  induction k with
  | zero => simp
  | succ j ih =>
      have hstep : M + (j + 1) = (M + j) + 1 := by ring
      rw [hstep, homogSum_succ, ih, hconst (M + j + 1) (by omega) (by omega)]
      push_cast
      ring

/-- **Unbounded discrepancy for sequences eventually constant along a progression.** -/
