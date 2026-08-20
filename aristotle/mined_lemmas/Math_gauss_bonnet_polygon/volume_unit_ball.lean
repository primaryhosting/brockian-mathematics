import RequestProject.Wedge

/-!
# Girard's relation for a solid cone over a spherical triangle

Given three vectors `u v w` in `ℝ³` in general position, the region
`Reg u v w`, the part of the unit ball where the three linear forms `⟪u,·⟫`, `⟪v,·⟫`, `⟪w,·⟫`
are nonnegative, has volume `((π - angle v w) + (π - angle u w) + (π - angle u v) - π)/3`.

This is Girard's theorem in disguise: the three quantities `π - angle · ·` are the dihedral
angles of the cone, and three times the volume of the cone is the area of the spherical
triangle it cuts out on the unit sphere.
-/

open MeasureTheory Metric Set Real InnerProductGeometry

namespace Math

/-- The closed half-space with inner normal `n`. -/

theorem volume_unit_ball : (volume (ball (0 : E3) 1)) = ENNReal.ofReal (4 / 3 * π) := by
  have h : Real.Gamma (3 / 2 + 1) = 3 / 4 * √π := by
    rw [Real.Gamma_add_one (by norm_num), show (3 : ℝ) / 2 = 1 / 2 + 1 by norm_num,
      Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
    ring
  rw [EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin, Nat.cast_ofNat, h]
  rw [show (√π) ^ 3 / (3 / 4 * √π) = 4 / 3 * (√π * √π) by
      field_simp [Real.sqrt_ne_zero'.2 Real.pi_pos],
    Real.mul_self_sqrt Real.pi_pos.le]
  simp

/-- The total area of the unit sphere in `ℝ³` is `4 * π`. -/
