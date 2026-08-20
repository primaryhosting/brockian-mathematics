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

theorem homogSum_completelyMultiplicative {f : ℕ → ℤ} (h : CompletelyMultiplicative f)
    {d : ℕ} (hd : 1 ≤ d) : ∀ n : ℕ, homogSum f d n = f d * homogSum f 1 n := by
  intro n
  induction n with
  | zero => simp [homogSum]
  | succ m ih =>
      rw [homogSum_succ, homogSum_succ, ih, h (m + 1) d (by omega) hd, mul_one]
      ring

/-- **Reduction for completely multiplicative sequences.** Such a `±1` sequence has
unbounded discrepancy iff its ordinary partial sums `f 1 + ⋯ + f n` are unbounded. -/
