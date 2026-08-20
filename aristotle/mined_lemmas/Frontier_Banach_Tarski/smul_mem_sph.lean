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

theorem smul_mem_sph (M : SO3) {x : E} (hx : x ∈ sph) : M • x ∈ sph := by
  show ‖M • x‖ = 1
  rw [norm_smul_so3]
  exact hx

