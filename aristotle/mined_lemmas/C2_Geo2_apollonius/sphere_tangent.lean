import Mathlib
namespace C2.Geo2

/-- Apollonius / parallelogram identity.
Statement fix: `(a+b)/2` is not well-typed in a general real inner product space
(there is no `Div V`), so it is written as the scalar multiple `(1/2 : ℝ) • (a+b)`. -/

theorem sphere_tangent {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (a b : V)
    (h : (inner ℝ a b : ℝ) = 0) : ‖a-b‖^2 = ‖a‖^2 + ‖b‖^2 := by
  rw [norm_sub_sq_real, h]; ring

end C2.Geo2

