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

theorem inner_smul_smul (M : SO3) (x y : E) :
    (inner ℝ (M • x) (M • y) : ℝ) = inner ℝ x y := by
  rw [inner_eq_dotProduct, inner_eq_dotProduct, smul_ofLp, smul_ofLp, dotProduct_mulVec,
    ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, so3_transpose_mul, Matrix.one_mulVec]

