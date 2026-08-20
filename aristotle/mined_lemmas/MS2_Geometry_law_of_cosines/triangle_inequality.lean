import Mathlib
namespace MS2.Geometry

/-- Law of cosines in an inner product space over `ℝ`. -/

theorem triangle_inequality {V : Type*} [NormedAddCommGroup V] (a b : V) :
    ‖a+b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b

/-- The Cauchy–Schwarz inequality. -/
