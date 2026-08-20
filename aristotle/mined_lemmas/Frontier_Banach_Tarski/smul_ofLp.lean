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

theorem smul_ofLp (M : SO3) (x : E) :
    (M • x).ofLp = (M : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x.ofLp := rfl

