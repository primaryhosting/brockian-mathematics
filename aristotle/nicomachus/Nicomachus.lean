import Mathlib
namespace Brockian.Nicomachus
/-- Nicomachus's theorem: the square of the n-th triangular number equals the sum of the first n cubes. -/
theorem sq_sum_eq_sum_cubes (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), k) ^ 2 = ∑ k ∈ Finset.range (n + 1), k ^ 3 := by
  sorry
end Brockian.Nicomachus
