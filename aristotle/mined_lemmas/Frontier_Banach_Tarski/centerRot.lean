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

def centerRot : Iso3 :=
  ((IsometryEquiv.constVAdd (-cVec) : E ≃ᵢ E).trans (rotIso (rZ 1))).trans
    (IsometryEquiv.constVAdd cVec : E ≃ᵢ E)

