import Mathlib
namespace Brockian.FrobeniusAbove
/-- Every integer strictly above the Frobenius number ab−a−b is a nonneg combination of a,b. -/
theorem frobenius_above (a b : ℕ) (ha : 1 < a) (hb : 1 < b)
    (hcop : Nat.Coprime a b) (m : ℕ) (hm : a * b - a - b < m) :
    ∃ x y : ℕ, a * x + b * y = m := by
  sorry
end Brockian.FrobeniusAbove
