import Mathlib
namespace C2.Geo2

/-- Apollonius / parallelogram identity.
Statement fix: `(a+b)/2` is not well-typed in a general real inner product space
(there is no `Div V`), so it is written as the scalar multiple `(1/2 : ℝ) • (a+b)`. -/

theorem apollonius {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (a b : V) :
    ‖a‖^2 + ‖b‖^2 = 2*‖(1/2 : ℝ) • (a+b)‖^2 + 2*‖(1/2 : ℝ) • (a-b)‖^2 := by
  rw [norm_smul, norm_smul, mul_pow, mul_pow, norm_add_sq_real, norm_sub_sq_real]
  norm_num
  ring

/-- Real polarization identity. Statement fix: in current Mathlib `inner` takes the
scalar field explicitly, so `inner a b` becomes `inner ℝ a b`. -/
