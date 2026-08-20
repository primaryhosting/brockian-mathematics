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

noncomputable def letterMat (x : Fin 2 × Bool) : Matrix (Fin 3) (Fin 3) ℝ :=
  if x.2 then (if x.1 = 0 then rotA else rotB) else (if x.1 = 0 then rotA else rotB)ᵀ

