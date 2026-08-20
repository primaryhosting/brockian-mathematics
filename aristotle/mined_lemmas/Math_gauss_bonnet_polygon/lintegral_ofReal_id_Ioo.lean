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

private theorem lintegral_ofReal_id_Ioo (a : ℝ) (ha : 0 ≤ a) :
    ∫⁻ x in Ioo (0 : ℝ) a, ENNReal.ofReal x = ENNReal.ofReal (a ^ 2 / 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ha, integral_id]
    ring
  · exact (continuous_id.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx using le_of_lt hx.1

/-- The area of the sector of the disc of squared radius `s` cut out by the two half planes
`0 ≤ p.1` and `0 ≤ cos θ * p.1 + sin θ * p.2` is `(π - θ) / 2 * s`. -/
