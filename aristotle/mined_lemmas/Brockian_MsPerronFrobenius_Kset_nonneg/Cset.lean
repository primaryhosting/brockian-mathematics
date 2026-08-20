import Mathlib

namespace Brockian.MsPerronFrobenius

open Matrix Finset

/-- Probability vectors all of whose coordinates are at least `δ`. -/

def Cset (M : Matrix (Fin n) (Fin n) ℝ) (δ : ℝ) : Set (ℝ × (Fin n → ℝ)) :=
  {p | 0 ≤ p.1 ∧ p.2 ∈ Kset n δ ∧ ∀ i, p.1 * p.2 i ≤ M.mulVec p.2 i}

