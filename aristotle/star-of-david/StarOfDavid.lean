import Mathlib
namespace Brockian.StarOfDavid
/-- The Star of David theorem: the two alternating triples of binomial coefficients surrounding
    an entry of Pascal's triangle have equal gcd. -/
theorem star_of_david (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    Nat.gcd (Nat.gcd (Nat.choose (n - 1) (k - 1)) (Nat.choose n (k + 1))) (Nat.choose (n + 1) k)
      = Nat.gcd (Nat.gcd (Nat.choose (n - 1) k) (Nat.choose n (k - 1))) (Nat.choose (n + 1) (k + 1)) := by
  sorry
end Brockian.StarOfDavid
