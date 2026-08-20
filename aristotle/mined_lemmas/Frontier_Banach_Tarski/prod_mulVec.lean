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

theorem prod_mulVec (L : List (Fin 2 × Bool)) :
    (L.map letterMat).prod *ᵥ vecR (0, 1, 0) = (((3 : ℝ)⁻¹) ^ L.length) • vecR (stateOf L) := by
  induction L with
  | nil => simp
  | cons x t ih =>
      rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul,
        letterMat_mulVec, stateOf_cons, List.length_cons, smul_smul, pow_succ]

