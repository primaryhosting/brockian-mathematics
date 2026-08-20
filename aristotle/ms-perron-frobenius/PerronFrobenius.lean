import Mathlib
namespace Brockian.MsPerronFrobenius
/-- Perron's theorem (positive case): a square matrix with strictly positive real entries has a
    positive real eigenvalue with a strictly positive eigenvector. -/
theorem perron (n : ℕ) (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ) (hpos : ∀ i j, 0 < M i j) :
    ∃ (l : ℝ) (v : Fin n → ℝ), 0 < l ∧ (∀ i, 0 < v i) ∧ M.mulVec v = l • v := by
  sorry
end Brockian.MsPerronFrobenius
