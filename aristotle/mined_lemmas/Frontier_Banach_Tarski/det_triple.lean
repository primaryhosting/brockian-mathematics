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

theorem det_triple (u v : Fin 3 → ℝ) :
    (Matrix.of ![u, v, u ⨯₃ v]).det = (u ⬝ᵥ u) * (v ⬝ᵥ v) - (u ⬝ᵥ v) ^ 2 := by
  simp [Matrix.det_fin_three, cross_apply, dotProduct, Fin.sum_univ_three]
  ring

/-- A rotation fixing two vectors with nondegenerate Gram determinant is the identity. -/
