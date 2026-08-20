import Mathlib
namespace C6.Geo4

/-- The norm of a vector in a normed additive commutative group is nonnegative. -/

theorem inner_comm_real {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (a b : V) :
    (inner ℝ a b : ℝ) = inner ℝ b a :=
  real_inner_comm b a

end C6.Geo4

