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

theorem smul_sph (M : SO3) : M • sph = sph := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact smul_mem_sph M hy
  · intro hx
    refine ⟨M⁻¹ • x, smul_mem_sph M⁻¹ hx, ?_⟩
    show M • (M⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel, one_smul]

/-- A nonidentity rotation fixes at most two points of the sphere. -/
