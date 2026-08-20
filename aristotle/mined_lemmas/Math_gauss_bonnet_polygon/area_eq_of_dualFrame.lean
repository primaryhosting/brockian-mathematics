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

theorem area_eq_of_dualFrame (hd : 0 < d)
    (hua : (inner ℝ u a : ℝ) = d) (hub : (inner ℝ u b : ℝ) = 0) (huc : (inner ℝ u c : ℝ) = 0)
    (hva : (inner ℝ v a : ℝ) = 0) (hvb : (inner ℝ v b : ℝ) = d) (hvc : (inner ℝ v c : ℝ) = 0)
    (hwa : (inner ℝ w a : ℝ) = 0) (hwb : (inner ℝ w b : ℝ) = 0) (hwc : (inner ℝ w c : ℝ) = d)
    (hspan : ∀ x : E3, ∃ p q r : ℝ, x = p • a + q • b + r • c) :
    (volume.toSphere (sphericalTriangle a b c)).toReal
      = (π - angle v w) + (π - angle u w) + (π - angle u v) - π := by
  have hcone := mem_cone_iff hd hua hub huc hva hvb hvc hwa hwb hwc hspan
  have hTmeas : MeasurableSet (sphericalTriangle a b c) := by
    have : sphericalTriangle a b c
        = (Subtype.val : sphere (0 : E3) 1 → E3) ⁻¹' (Hs u ∩ Hs v ∩ Hs w) := by
      ext x
      simp only [sphericalTriangle, mem_setOf_eq, mem_preimage, mem_inter_iff, Hs, and_assoc]
      exact hcone (x : E3)
    rw [this]
    exact (measurable_subtype_coe
      (((measurableSet_Hs u).inter (measurableSet_Hs v)).inter (measurableSet_Hs w)))
  rw [Measure.toSphere_apply' _ hTmeas,
    smul_triangle_eq hd hua hub huc hva hvb hvc hwa hwb hwc hspan,
    measure_diff_null (measure_singleton 0)]
  rw [show Module.finrank ℝ E3 = 3 from finrank_euclideanSpace_fin]
  rw [ENNReal.toReal_mul]
  have hne : u ≠ 0 := ne_zero_of_inner_ne_zero (ne_of_gt hd) hua
  have hnv : v ≠ 0 := ne_zero_of_inner_ne_zero (ne_of_gt hd) hvb
  have huv : ∀ r : ℝ, v ≠ r • u := not_parallel_of_dual (ne_of_gt hd) hua hva hvb
  have huw : ∀ r : ℝ, w ≠ r • u := not_parallel_of_dual (ne_of_gt hd) hua hwa hwc
  have hvw : ∀ r : ℝ, w ≠ r • v := not_parallel_of_dual (ne_of_gt hd) hvb hwb hwc
  have := volume_Reg u v w hne hnv huv huw hvw
  simp only [ENNReal.toReal_natCast]
  push_cast
  linarith

end DualFrame


/-! ### The Gauss–Bonnet theorem for a spherical triangle -/

/-- `‖x × a‖ = ‖x - ⟪a,x⟫ a‖` for a unit vector `a`. -/
