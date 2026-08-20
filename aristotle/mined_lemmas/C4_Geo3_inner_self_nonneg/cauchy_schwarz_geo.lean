import Mathlib
namespace C4.Geo3

/-- The inner product of a vector with itself is nonnegative. -/

theorem cauchy_schwarz_geo {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (a b : V) :
    (inner ℝ a b : ℝ)^2 ≤ (inner ℝ a a : ℝ) * (inner ℝ b b : ℝ) := by
  rw [sq]
  exact real_inner_mul_inner_self_le a b

end C4.Geo3

