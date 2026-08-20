import Mathlib
namespace Brockian.MsCatalanSquareSum
/-- The sum of squares of a row of Pascal's triangle: ∑_k C(n,k)² = C(2n,n). -/
theorem sum_choose_sq (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (Nat.choose n k) ^ 2 = Nat.choose (2 * n) n := by
  sorry
end Brockian.MsCatalanSquareSum
