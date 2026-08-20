import Mathlib
namespace C5.An7

theorem abs_le_of_sq_le (a b : ℝ) (h : a^2 ≤ b^2) (hb : 0 ≤ b) : -b ≤ a ∧ a ≤ b := by
  constructor <;> nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
end C5.An7

