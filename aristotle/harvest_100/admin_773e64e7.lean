import Mathlib

namespace Math

/-- The prime 101 is a sum of two squares: `101 = 1 ^ 2 + 10 ^ 2`. -/
theorem two_squares_101 : Nat.Prime 101 ∧ ∃ a b : ℕ, 101 = a ^ 2 + b ^ 2 := by
  refine ⟨by norm_num, 1, 10, by norm_num⟩

end Math

