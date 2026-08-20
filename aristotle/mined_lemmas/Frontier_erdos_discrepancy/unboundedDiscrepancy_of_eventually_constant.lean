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

theorem unboundedDiscrepancy_of_eventually_constant {f : ℕ → ℤ} (hf : IsPMOne f)
    {d M : ℕ} {c : ℤ} (hd : 1 ≤ d) (hc : c = 1 ∨ c = -1)
    (hconst : ∀ i, M ≤ i → 1 ≤ i → f (i * d) = c) : UnboundedDiscrepancy f := by
  intro C
  refine ⟨d, M + (C + M + 1), hd, by omega, ?_⟩
  have hA : (homogSum f d M).natAbs ≤ M := homogSum_natAbs_le hf hd M
  rw [homogSum_eventually_constant hconst]
  rcases hc with h | h <;> subst h <;> push_cast <;> omega

/-! ### Eventually periodic and periodic sequences -/

/-- An eventually periodic sequence is eventually constant along the progression whose
difference is the period. -/
