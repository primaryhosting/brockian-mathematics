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

theorem apply_mul_eventually_period {f : ℕ → ℤ} {p M : ℕ} (hp : 1 ≤ p)
    (hper : ∀ n, M ≤ n → f (n + p) = f n) :
    ∀ i, M + 1 ≤ i → 1 ≤ i → f (i * p) = f ((M + 1) * p) := by
  intro i hi _
  induction i with
  | zero => omega
  | succ m ih =>
      rcases Nat.eq_or_lt_of_le hi with h | h
      · rw [← h]
      · have hm : M + 1 ≤ m := by omega
        have hstep : (m + 1) * p = m * p + p := by ring
        have hMle : M ≤ m * p := le_trans (by omega) (Nat.le_mul_of_pos_right m hp)
        rw [hstep, hper (m * p) hMle, ih hm (by omega)]

/-- **The Erdős discrepancy statement holds for eventually periodic `±1` sequences.** -/
