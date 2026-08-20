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

theorem le_discrepancyUpTo {f : ℕ → ℤ} {d n N : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n)
    (h : n * d ≤ N) : (homogSum f d n).natAbs ≤ discrepancyUpTo f N := by
  have hdN : d ≤ N := le_trans (Nat.le_mul_of_pos_left d hn) h
  have hnN : n ≤ N := le_trans (Nat.le_mul_of_pos_right n hd) h
  have hmem : (n, d) ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N) := by
    simp [Finset.mem_product, hd, hn, hdN, hnN]
  have := Finset.le_sup (f := fun p : ℕ × ℕ =>
    if p.1 * p.2 ≤ N then (homogSum f p.2 p.1).natAbs else 0) hmem
  simpa [h] using this

/-- Conversely, a large discrepancy is witnessed by an actual homogeneous progression. -/
