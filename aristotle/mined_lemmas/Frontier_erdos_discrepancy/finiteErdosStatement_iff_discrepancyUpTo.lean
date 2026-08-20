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

theorem finiteErdosStatement_iff_discrepancyUpTo :
    FiniteErdosStatement ↔
      ∀ C : ℕ, ∃ N : ℕ, ∀ f : ℕ → ℤ, IsPMOne f → C < discrepancyUpTo f N := by
  constructor
  · intro h C
    obtain ⟨N, hN⟩ := h C
    refine ⟨N, fun f hf => ?_⟩
    obtain ⟨d, n, hd, hn, hnd, hlt⟩ := hN f hf
    exact lt_of_lt_of_le hlt (le_discrepancyUpTo hd hn hnd)
  · intro h C
    obtain ⟨N, hN⟩ := h C
    exact ⟨N, fun f hf => exists_of_lt_discrepancyUpTo (hN f hf)⟩

/-- **The Erdős discrepancy statement is equivalent to a uniform, finitary growth
statement for the discrepancy function.**  (The nontrivial implication is the compactness
argument of `Frontier.erdos_iff_finite`.) -/
