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

theorem homogSum_sub_natAbs_le {f g : ℕ → ℤ} (hf : IsPMOne f) (hg : IsPMOne g)
    {M d : ℕ} (hd : 1 ≤ d) (h : ∀ k, M ≤ k → f k = g k) :
    ∀ n : ℕ, (homogSum f d n - homogSum g d n).natAbs ≤ 2 * min n M := by
  intro n
  induction n with
  | zero => simp [homogSum]
  | succ m ih =>
      have hle : m + 1 ≤ (m + 1) * d := Nat.le_mul_of_pos_right _ hd
      have hpos : 1 ≤ (m + 1) * d := le_trans (by omega) hle
      rw [homogSum_succ, homogSum_succ]
      by_cases hcase : M ≤ (m + 1) * d
      · have heq := h _ hcase
        omega
      · have h1 := hf ((m + 1) * d) hpos
        have h2 := hg ((m + 1) * d) hpos
        omega

/-- **Unbounded discrepancy only depends on the tail of a sequence**: changing finitely
many values of a `±1` sequence does not affect it. -/
