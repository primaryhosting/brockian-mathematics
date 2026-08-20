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

theorem homogSum_natAbs_le {f : ℕ → ℤ} (hf : IsPMOne f) {d : ℕ} (hd : 1 ≤ d) :
    ∀ n : ℕ, (homogSum f d n).natAbs ≤ n := by
  intro n
  induction n with
  | zero => simp [homogSum]
  | succ m ih =>
      have hpos : 1 ≤ (m + 1) * d := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have hv := hf ((m + 1) * d) hpos
      rw [homogSum_succ]
      omega

/-- If `f` is constant equal to `c` on the tail `{i * d : i ≥ M}` of a homogeneous
progression, its partial sums along that progression grow linearly. -/
