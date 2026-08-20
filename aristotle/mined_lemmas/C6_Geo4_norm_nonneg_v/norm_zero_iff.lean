import Mathlib
namespace C6.Geo4

/-- The norm of a vector in a normed additive commutative group is nonnegative. -/

theorem norm_zero_iff {V : Type*} [NormedAddCommGroup V] (a : V) : ‖a‖ = 0 ↔ a = 0 :=
  norm_eq_zero

/-- Symmetry of the real inner product.
Note: the scalar field is now an explicit argument of `inner` in current Mathlib,
so the statement is written `inner ℝ a b`. -/
