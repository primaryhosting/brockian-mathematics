import Mathlib
namespace C4.Geo3

/-- The inner product of a vector with itself is nonnegative. -/

theorem inner_self_nonneg {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (a : V) :
    0 ≤ (inner ℝ a a : ℝ) :=
  real_inner_self_nonneg

/-- Scaling a vector by a real number scales its norm by the absolute value. -/
