import Mathlib
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/
theorem sum_three_squares_iff (n : ℕ) :
    (∃ a b c : ℕ, n = a ^ 2 + b ^ 2 + c ^ 2) ↔ ¬ ∃ k m : ℕ, n = 4 ^ k * (8 * m + 7) := by
  sorry
end Brockian.LegendreThreeSquare
