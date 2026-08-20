import Mathlib
namespace Brockian.GaussEureka
/-- Gauss' Eureka theorem: every natural number is a sum of three triangular numbers. -/
theorem sum_three_triangular (n : ℕ) :
    ∃ a b c : ℕ, n = a * (a + 1) / 2 + b * (b + 1) / 2 + c * (c + 1) / 2 := by
  sorry
end Brockian.GaussEureka
