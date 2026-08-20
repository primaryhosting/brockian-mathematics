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

theorem smul_triangle_eq (hd : 0 < d)
    (hua : (inner ℝ u a : ℝ) = d) (hub : (inner ℝ u b : ℝ) = 0) (huc : (inner ℝ u c : ℝ) = 0)
    (hva : (inner ℝ v a : ℝ) = 0) (hvb : (inner ℝ v b : ℝ) = d) (hvc : (inner ℝ v c : ℝ) = 0)
    (hwa : (inner ℝ w a : ℝ) = 0) (hwb : (inner ℝ w b : ℝ) = 0) (hwc : (inner ℝ w c : ℝ) = d)
    (hspan : ∀ x : E3, ∃ p q r : ℝ, x = p • a + q • b + r • c) :
    Ioo (0 : ℝ) 1 • ((↑) '' (sphericalTriangle a b c) : Set E3) = Reg u v w \ {0} := by
  have hcone := mem_cone_iff hd hua hub huc hva hvb hvc hwa hwb hwc hspan
  have hReg : ∀ z : E3, z ∈ Reg u v w ↔ (‖z‖ < 1 ∧ 0 ≤ (inner ℝ u z : ℝ) ∧
      0 ≤ (inner ℝ v z : ℝ) ∧ 0 ≤ (inner ℝ w z : ℝ)) := by
    intro z
    simp only [Reg, Wdg, Hs, mem_inter_iff, mem_ball_zero_iff, mem_setOf_eq, and_assoc]
  ext y
  constructor
  · rintro ⟨t, ht, x, hx, rfl⟩
    obtain ⟨x, hxs, rfl⟩ := hx
    have hxn : ‖(x : E3)‖ = 1 := mem_sphere_zero_iff_norm.1 x.2
    have hmem := (hcone (x : E3)).1 hxs
    refine ⟨(hReg _).2 ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [norm_smul, hxn, mul_one, Real.norm_eq_abs, abs_of_pos ht.1]
      exact ht.2
    · rw [real_inner_smul_right]; exact mul_nonneg ht.1.le hmem.1
    · rw [real_inner_smul_right]; exact mul_nonneg ht.1.le hmem.2.1
    · rw [real_inner_smul_right]; exact mul_nonneg ht.1.le hmem.2.2
    · simp only [mem_singleton_iff, smul_eq_zero, not_or]
      refine ⟨ne_of_gt ht.1, fun h => ?_⟩
      rw [h, norm_zero] at hxn
      exact zero_ne_one hxn
  · rintro ⟨hz, hy0'⟩
    obtain ⟨hyn1, hu, hv, hw⟩ := (hReg y).1 hz
    have hy0 : y ≠ 0 := by simpa using hy0'
    have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy0
    have hsph : ‖y‖⁻¹ • y ∈ sphere (0 : E3) 1 := by
      simp [norm_smul, inv_mul_cancel₀ (ne_of_gt hyn)]
    refine ⟨‖y‖, ⟨hyn, hyn1⟩, ‖y‖⁻¹ • y, ⟨⟨‖y‖⁻¹ • y, hsph⟩, ?_, rfl⟩, ?_⟩
    · refine (hcone _).2 ⟨?_, ?_, ?_⟩ <;> rw [real_inner_smul_right] <;>
        exact mul_nonneg (inv_pos.2 hyn).le (by assumption)
    · show ‖y‖ • (‖y‖⁻¹ • y) = y
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hyn), one_smul]

/-- The area of the spherical triangle, computed with the cone measure on the sphere. -/
