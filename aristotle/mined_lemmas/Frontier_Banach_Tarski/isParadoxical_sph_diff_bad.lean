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

theorem isParadoxical_sph_diff_bad : IsParadoxical SO3 (sph \ badSet) :=
  isParadoxical_of_free phi (sph \ badSet) (fun w _ hx => sph_diff_bad_invariant w hx)
    (fun w _ hx h => sph_diff_bad_free w hx h)

/-! ### Rotations about the coordinate axes -/

/-- Rotation by `t` about the `z`-axis. -/
