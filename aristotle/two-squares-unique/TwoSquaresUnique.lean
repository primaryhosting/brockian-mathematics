import Mathlib
namespace Brockian.TwoSquaresUnique
/-- Uniqueness in Fermat's two-square theorem: a prime p ≡ 1 (mod 4) has an essentially unique
    representation as a sum of two squares (ordered a ≤ b). -/
theorem two_squares_unique {p a b c d : ℕ} (hp : p.Prime) (hp1 : p % 4 = 1)
    (hab : p = a ^ 2 + b ^ 2) (hcd : p = c ^ 2 + d ^ 2)
    (h1 : a ≤ b) (h2 : c ≤ d) : a = c ∧ b = d := by
  sorry
end Brockian.TwoSquaresUnique
