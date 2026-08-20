/-
Absorbing the countable set of poles: the unit sphere is `SO(3)`-paradoxical.
-/
import RequestProject.Sphere

open Matrix Set Pointwise

namespace BT

noncomputable section

/-! ### Countability of the solution sets of rotation equations -/

/-- For a point `d` off the `z`-axis, only countably many angles `t` satisfy
`rZ (c * t) • d = d'`. -/

theorem inner_eq_dotProduct (x y : E) : (inner ℝ x y : ℝ) = x.ofLp ⬝ᵥ y.ofLp := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

