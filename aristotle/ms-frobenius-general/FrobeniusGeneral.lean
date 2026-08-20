import Mathlib
namespace Brockian.MsFrobeniusGeneral
/-- The general Frobenius / numerical-semigroup theorem: for positive a,b,c with gcd(a,b,c)=1,
    every sufficiently large integer is a nonnegative combination a·x + b·y + c·z. -/
theorem frobenius_three (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hg : Nat.gcd a (Nat.gcd b c) = 1) :
    ∃ N : ℕ, ∀ m : ℕ, N < m → ∃ x y z : ℕ, a * x + b * y + c * z = m := by
  sorry
end Brockian.MsFrobeniusGeneral
