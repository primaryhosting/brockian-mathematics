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

def rotIso (M : SO3) : Iso3 where
  toFun := fun x => M • x
  invFun := fun x => M⁻¹ • x
  left_inv := fun x => by
    show M⁻¹ • (M • x) = x
    rw [smul_smul, inv_mul_cancel, one_smul]
  right_inv := fun x => by
    show M • (M⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel, one_smul]
  isometry_toFun := by
    refine Isometry.of_dist_eq fun x y => ?_
    show dist (M • x) (M • y) = dist x y
    rw [dist_eq_norm, dist_eq_norm, ← so3_smul_sub, norm_smul_so3]

