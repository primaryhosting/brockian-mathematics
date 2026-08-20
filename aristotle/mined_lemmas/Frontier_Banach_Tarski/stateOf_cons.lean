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

@[simp] theorem stateOf_cons (x : Fin 2 × Bool) (L : List (Fin 2 × Bool)) :
    stateOf (x :: L) = step x (stateOf L) := rfl

/-- The real vector attached to an integer state. -/
