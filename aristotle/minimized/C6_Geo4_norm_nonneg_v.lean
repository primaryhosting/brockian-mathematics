import Mathlib
namespace C6.Geo4

/-- The norm of a vector in a normed additive commutative group is nonnegative. -/

theorem norm_nonneg_v {V : Type*} [NormedAddCommGroup V] (a : V) : 0 ≤ ‖a‖ :=
  norm_nonneg a

/-- A vector has zero norm iff it is the zero vector. -/
