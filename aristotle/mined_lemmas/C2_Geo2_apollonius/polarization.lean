import Mathlib
namespace C2.Geo2

/-- Apollonius / parallelogram identity.
Statement fix: `(a+b)/2` is not well-typed in a general real inner product space
(there is no `Div V`), so it is written as the scalar multiple `(1/2 : ℝ) • (a+b)`. -/

theorem polarization {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (a b : V) :
    (inner ℝ a b : ℝ) = (‖a+b‖^2 - ‖a-b‖^2)/4 := by
  rw [norm_add_sq_real, norm_sub_sq_real]; ring

/-- Pythagoras: orthogonal vectors satisfy `‖a-b‖² = ‖a‖² + ‖b‖²`. -/
