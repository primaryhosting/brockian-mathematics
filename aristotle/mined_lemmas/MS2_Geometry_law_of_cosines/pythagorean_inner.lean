import Mathlib
namespace MS2.Geometry

/-- Law of cosines in an inner product space over `ℝ`. -/

theorem pythagorean_inner {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (a b : V)
    (h : inner ℝ a b = (0:ℝ)) : ‖a+b‖^2 = ‖a‖^2 + ‖b‖^2 := by
  rw [norm_add_sq_real, h]; ring

/-- The triangle inequality. -/
