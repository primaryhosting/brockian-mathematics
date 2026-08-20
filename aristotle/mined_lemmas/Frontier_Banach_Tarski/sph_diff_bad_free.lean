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

theorem sph_diff_bad_free (w : F2) {x : E} (hx : x ∈ sph \ badSet) (h : phi w • x = x) : w = 1 := by
  by_contra hw
  exact hx.2 ⟨hx.1, w, hw, h⟩

