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

theorem erdosDiscrepancyStatement_iff_discrepancyUpTo :
    ErdosDiscrepancyStatement ↔
      ∀ f : ℕ → ℤ, IsPMOne f → ∀ C : ℕ, ∃ N : ℕ, C < discrepancyUpTo f N := by
  constructor
  · intro h f hf C
    obtain ⟨d, n, hd, hn, hlt⟩ := h f hf C
    exact ⟨n * d, lt_of_lt_of_le hlt (le_discrepancyUpTo hd hn le_rfl)⟩
  · intro h f hf C
    obtain ⟨N, hN⟩ := h f hf C
    obtain ⟨d, n, hd, hn, _, hlt⟩ := exists_of_lt_discrepancyUpTo hN
    exact ⟨d, n, hd, hn, hlt⟩

/-- **Base case, in terms of the discrepancy function**: every `±1` sequence has
discrepancy at least `2` already within `{1, …, 12}`. -/
