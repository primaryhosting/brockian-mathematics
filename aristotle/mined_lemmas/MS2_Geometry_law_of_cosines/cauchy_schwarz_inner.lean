import Mathlib
namespace MS2.Geometry

/-- Law of cosines in an inner product space over `ℝ`. -/

theorem cauchy_schwarz_inner {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (a b : V) :
    |inner ℝ a b| ≤ ‖a‖ * ‖b‖ := abs_real_inner_le_norm a b

end MS2.Geometry

