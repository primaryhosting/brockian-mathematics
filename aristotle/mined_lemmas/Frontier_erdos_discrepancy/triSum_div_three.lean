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

theorem triSum_div_three (n : ℕ) :
    triSum (n / 3) ≤ triSum n ∧ triSum n ≤ triSum (n / 3) + 1 := by
  rcases (show n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 by omega) with h | h | h
  · obtain ⟨m, rfl⟩ : ∃ m, n = 3 * m := ⟨n / 3, by omega⟩
    rw [show 3 * m / 3 = m from by omega, triSum_three_mul]
    omega
  · obtain ⟨m, rfl⟩ : ∃ m, n = 3 * m + 1 := ⟨n / 3, by omega⟩
    rw [show (3 * m + 1) / 3 = m from by omega, triSum_three_mul_add_one]
    omega
  · obtain ⟨m, rfl⟩ : ∃ m, n = 3 * m + 2 := ⟨n / 3, by omega⟩
    rw [show (3 * m + 2) / 3 = m from by omega, triSum_three_mul_add_two]
    omega

/-- The partial sums of the base-`3` sequence are nonnegative. -/
