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

theorem inv_of_eq_mk (i : Fin 2) : (FreeGroup.of i : F2)⁻¹ = FreeGroup.mk [(i, false)] := by
  rw [of_eq_mk, FreeGroup.inv_mk]
  rfl

/-- Every element of `F2` either starts with the letter `i`, or is `i` times an element
starting with `i⁻¹`. -/
