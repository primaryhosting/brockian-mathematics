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

theorem unboundedDiscrepancy_completelyMultiplicative_iff {f : ℕ → ℤ}
    (h : CompletelyMultiplicative f) (hf : IsPMOne f) :
    UnboundedDiscrepancy f ↔ ∀ C : ℕ, ∃ n : ℕ, 1 ≤ n ∧ C < (homogSum f 1 n).natAbs := by
  constructor
  · intro hU C
    obtain ⟨d, n, hd, hn, hlt⟩ := hU C
    refine ⟨n, hn, ?_⟩
    rw [homogSum_completelyMultiplicative h hd n, Int.natAbs_mul] at hlt
    rcases hf d hd with hv | hv <;> rw [hv] at hlt <;> simpa using hlt
  · intro hS C
    obtain ⟨n, hn, hlt⟩ := hS C
    exact ⟨1, n, le_rfl, hn, hlt⟩

/-! ### Invariance under changing finitely many values -/

/-- Two `±1` sequences that agree from `M` on have homogeneous sums differing by at most
`2 * M`. -/
