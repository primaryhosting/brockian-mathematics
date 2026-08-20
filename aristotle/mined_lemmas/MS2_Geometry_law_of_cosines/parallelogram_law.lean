import Mathlib
namespace MS2.Geometry

/-- Law of cosines in an inner product space over `ℝ`. -/

theorem parallelogram_law {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (a b : V) :
    ‖a+b‖^2 + ‖a-b‖^2 = 2*‖a‖^2 + 2*‖b‖^2 := by
  rw [norm_add_sq_real, norm_sub_sq_real]; ring

/-- Pythagoras' theorem for orthogonal vectors. -/
