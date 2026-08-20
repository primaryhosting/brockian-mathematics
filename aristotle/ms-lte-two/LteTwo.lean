import Mathlib
namespace Brockian.LteTwo
/-- Lifting the exponent for p = 2: for odd a,b with 4 ∣ a−b (b ≤ a) and even n,
    v₂(aⁿ − bⁿ) = v₂(a−b) + v₂(n). -/
theorem lte_two {a b n : ℕ} (ha : Odd a) (hb : Odd b) (hab : 4 ∣ (a - b))
    (hle : b ≤ a) (hn : 0 < n) :
    (a ^ n - b ^ n).factorization 2 = (a - b).factorization 2 + n.factorization 2 := by
  sorry
end Brockian.LteTwo
