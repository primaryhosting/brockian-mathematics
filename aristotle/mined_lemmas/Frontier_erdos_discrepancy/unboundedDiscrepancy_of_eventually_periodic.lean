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

theorem unboundedDiscrepancy_of_eventually_periodic {f : ℕ → ℤ} {p M : ℕ} (hp : 1 ≤ p)
    (hper : ∀ n, M ≤ n → f (n + p) = f n) (hf : IsPMOne f) : UnboundedDiscrepancy f := by
  have hpos : 1 ≤ (M + 1) * p := Nat.one_le_iff_ne_zero.mpr (by positivity)
  exact unboundedDiscrepancy_of_eventually_constant hf hp (hf ((M + 1) * p) hpos)
    (apply_mul_eventually_period hp hper)

/-- **The Erdős discrepancy statement holds for periodic `±1` sequences.** -/
