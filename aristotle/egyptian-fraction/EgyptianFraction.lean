import Mathlib
namespace Brockian.EgyptianFraction
/-- Egyptian fraction existence: every rational a/b with 0 < a < b is a finite sum of
    distinct unit fractions (the Finset of denominators makes them automatically distinct). -/
theorem egyptian_fraction (a b : ℕ) (ha : 0 < a) (hab : a < b) :
    ∃ S : Finset ℕ, (∀ d ∈ S, 0 < d) ∧ ∑ d ∈ S, (1 / (d : ℚ)) = (a : ℚ) / b := by
  sorry
end Brockian.EgyptianFraction
