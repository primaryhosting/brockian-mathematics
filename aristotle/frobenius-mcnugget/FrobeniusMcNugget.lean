import Mathlib
namespace Brockian.FrobeniusMcNugget
/-- The Frobenius number ab−a−b of coprime a,b>1 is not a nonnegative integer combination. -/
theorem frobenius_not_representable (a b : ℕ) (ha : 1 < a) (hb : 1 < b)
    (hcop : Nat.Coprime a b) : ¬ ∃ x y : ℕ, a * x + b * y = a * b - a - b := by
  sorry
end Brockian.FrobeniusMcNugget
