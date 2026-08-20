import Mathlib
namespace MS2.Geometry

/-- Law of cosines in an inner product space over `ℝ`. -/

theorem law_of_cosines {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (a b : V) :
    ‖a - b‖^2 = ‖a‖^2 + ‖b‖^2 - 2 * inner ℝ a b := by
  rw [norm_sub_sq_real]; ring

/-- The parallelogram law. -/
