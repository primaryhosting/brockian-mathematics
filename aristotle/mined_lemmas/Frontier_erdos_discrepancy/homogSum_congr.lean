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

theorem homogSum_congr {f g : ℕ → ℤ} {d : ℕ} (hd : 1 ≤ d) :
    ∀ {n : ℕ}, (∀ k, 1 ≤ k → k ≤ n * d → f k = g k) → homogSum f d n = homogSum g d n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ m ih =>
      intro h
      have hpos : 1 ≤ (m + 1) * d := Nat.one_le_iff_ne_zero.mpr (by positivity)
      rw [homogSum_succ, homogSum_succ, ih ?_, h ((m + 1) * d) hpos le_rfl]
      intro k hk1 hk2
      exact h k hk1 (hk2.trans (Nat.mul_le_mul_right d (Nat.le_succ m)))

/-- Easy direction: the finitary statement implies the infinite one. -/
