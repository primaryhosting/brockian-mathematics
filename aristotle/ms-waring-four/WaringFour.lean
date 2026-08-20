import Mathlib
namespace Brockian.MsWaringFour
/-- Waring's problem for fourth powers, g(4) = 19: every natural number is a sum of 19 fourth
    powers. -/
theorem waring_four (n : ℕ) : ∃ f : Fin 19 → ℕ, n = ∑ i, (f i) ^ 4 := by
  sorry
end Brockian.MsWaringFour
