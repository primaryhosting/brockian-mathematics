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

theorem equidec_sph_diff {D : Set E} (hD : D ⊆ sph) (hcount : D.Countable) :
    Equidec SO3 sph (sph \ D) := by
  obtain ⟨rho, hrho⟩ := exists_absorbing_rotation hD hcount
  refine Equidec.absorb rho (fun n => ?_) hrho
  rintro _ ⟨d, hd, rfl⟩
  exact smul_mem_sph _ (hD hd)

/-- **The Hausdorff paradox**: the unit sphere is `SO(3)`-paradoxical. -/
