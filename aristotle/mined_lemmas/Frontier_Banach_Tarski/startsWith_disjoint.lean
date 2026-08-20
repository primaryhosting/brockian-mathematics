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

theorem startsWith_disjoint {x y : Fin 2 × Bool} (h : x ≠ y) :
    Disjoint (startsWith x) (startsWith y) := by
  rw [Set.disjoint_left]
  intro w hx hy
  exact h (by rw [← Option.some_inj, ← hx, ← hy])

