import Mathlib
namespace Brockian.TwoSquares
/-- Sum of two squares: n>0 is a² + b² iff every prime ≡ 3 (mod 4) in its factorization
    occurs to an even power. -/
theorem sum_two_squares_iff (n : ℕ) (hn : 0 < n) :
    (∃ a b : ℕ, n = a ^ 2 + b ^ 2) ↔
      ∀ p, p.Prime → p % 4 = 3 → Even (n.factorization p) := by
  sorry
end Brockian.TwoSquares
