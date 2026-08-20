import Mathlib

namespace Brockian.MsPerronFrobenius

open Matrix Finset

/-- Probability vectors all of whose coordinates are at least `δ`. -/

def Kset (n : ℕ) (δ : ℝ) : Set (Fin n → ℝ) := {x | (∀ i, δ ≤ x i) ∧ ∑ i, x i = 1}

variable {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}

