import Mathlib
namespace Brockian.MsPell
/-- Pell's equation is solvable: for a non-square positive d, x² − d·y² = 1 has a solution
    with y > 0. -/
theorem pell_solvable (d : ℕ) (hd : 0 < d) (hnsq : ¬ IsSquare d) :
    ∃ x y : ℤ, 0 < y ∧ x ^ 2 - (d : ℤ) * y ^ 2 = 1 := by
  sorry
end Brockian.MsPell
