import RequestProject.Sector

open MeasureTheory Metric Set Real InnerProductGeometry
open scoped ENNReal RealInnerProductSpace

namespace Math

/-- Euclidean three-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The volume of the standard solid wedge of dihedral angle `psi` inside the unit ball:
the axis of the wedge is the first coordinate axis, and the wedge is described in the plane
of the last two coordinates as the cone spanned by `(1,0)` and `(cos psi, sin psi)`. -/

theorem volume_sector (psi rho : ℝ) (h0 : 0 ≤ psi) (hpi : psi ≤ π) (hr : 0 ≤ rho) :
    volume {z : ℝ × ℝ | z.1 ^ 2 + z.2 ^ 2 < rho ^ 2 ∧ 0 ≤ z.2 ∧
        0 ≤ z.1 * Real.sin psi - z.2 * Real.cos psi} = ENNReal.ofReal (psi * rho ^ 2 / 2) := by
  set S : Set (ℝ × ℝ) := {z : ℝ × ℝ | z.1 ^ 2 + z.2 ^ 2 < rho ^ 2 ∧ 0 ≤ z.2 ∧
        0 ≤ z.1 * Real.sin psi - z.2 * Real.cos psi} with hS
  have hSm : MeasurableSet S := by rw [hS]; measurability
  have hAm : MeasurableSet (polarCoord.symm ⁻¹' S) :=
    hSm.preimage continuous_polarCoord_symm.measurable
  -- pass to polar coordinates
  have key := lintegral_comp_polarCoord_symm (S.indicator (1 : ℝ × ℝ → ℝ≥0∞))
  rw [lintegral_indicator_one hSm] at key
  have hpre : ∀ p : ℝ × ℝ, S.indicator (1 : ℝ × ℝ → ℝ≥0∞) (polarCoord.symm p)
      = (polarCoord.symm ⁻¹' S).indicator (1 : ℝ × ℝ → ℝ≥0∞) p := by
    intro p
    by_cases hp : polarCoord.symm p ∈ S
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (Set.mem_preimage.2 hp)]; rfl
    · rw [Set.indicator_of_notMem hp,
        Set.indicator_of_notMem (fun hc => hp (Set.mem_preimage.1 hc))]
  have step : ∫⁻ (p : ℝ × ℝ) in polarCoord.target, ENNReal.ofReal p.1 •
      S.indicator (1 : ℝ × ℝ → ℝ≥0∞) (polarCoord.symm p)
      = ∫⁻ p in (polarCoord.symm ⁻¹' S) ∩ polarCoord.target, ENNReal.ofReal p.1 := by
    simp only [hpre, smul_eq_mul]
    rw [show (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * (polarCoord.symm ⁻¹' S).indicator 1 p)
        = (polarCoord.symm ⁻¹' S).indicator (fun p : ℝ × ℝ => ENNReal.ofReal p.1) from ?_]
    · rw [lintegral_indicator hAm, Measure.restrict_restrict hAm]
    · funext p
      by_cases hp : p ∈ (polarCoord.symm ⁻¹' S) <;> simp [hp]
  -- the polar preimage of the sector is a rectangle
  have hregion : (polarCoord.symm ⁻¹' S) ∩ polarCoord.target
      = (Ioo 0 rho) ×ˢ (Ioo (-π) π ∩ Icc 0 psi) := by
    ext ⟨r, phi⟩
    simp only [polarCoord_target, polarCoord_symm_apply, mem_inter_iff, mem_prod, mem_Ioi,
      mem_Ioo, mem_Icc, mem_preimage, hS, mem_setOf_eq]
    constructor
    · rintro ⟨⟨hball, hsin, hsec⟩, hr0, hphi1, hphi2⟩
      have hsq : (r * cos phi) ^ 2 + (r * sin phi) ^ 2 = r ^ 2 := by
        have := sin_sq_add_cos_sq phi; nlinarith
      rw [hsq] at hball
      have hrlt : r < rho := by nlinarith
      have hsin' : 0 ≤ sin phi := nonneg_of_mul_nonneg_right hsin hr0
      have hphi0 : 0 ≤ phi := by
        by_contra hc
        push_neg at hc
        exact absurd hsin' (not_le.2 (sin_neg_of_neg_of_neg_pi_lt hc hphi1))
      have hsec' : 0 ≤ sin (psi - phi) := by
        have hexp : r * sin (psi - phi) = r * cos phi * sin psi - r * sin phi * cos psi := by
          rw [Real.sin_sub]; ring
        nlinarith [hsec]
      have hle : phi ≤ psi := by
        by_contra hc
        push_neg at hc
        exact absurd hsec' (not_le.2 (sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)))
      exact ⟨⟨hr0, hrlt⟩, ⟨hphi1, hphi2⟩, hphi0, hle⟩
    · rintro ⟨⟨hr0, hrlt⟩, ⟨hphi1, hphi2⟩, hphi0, hle⟩
      have hsq : (r * cos phi) ^ 2 + (r * sin phi) ^ 2 = r ^ 2 := by
        have := sin_sq_add_cos_sq phi; nlinarith
      have hsin' : 0 ≤ sin phi := sin_nonneg_of_nonneg_of_le_pi hphi0 (by linarith)
      have hsec' : 0 ≤ sin (psi - phi) :=
        sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
      refine ⟨⟨by rw [hsq]; nlinarith, by positivity, ?_⟩, hr0, hphi1, hphi2⟩
      have hexp : r * sin (psi - phi) = r * cos phi * sin psi - r * sin phi * cos psi := by
        rw [Real.sin_sub]; ring
      nlinarith
  -- compute the resulting integral over the rectangle
  rw [← key, step, hregion, Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod _ (by fun_prop)]
  simp only [setLIntegral_const, volume_angle_interval psi hpi]
  rw [lintegral_mul_const _ (by fun_prop)]
  have hradial : ∫⁻ x in Ioo (0 : ℝ) rho, ENNReal.ofReal x = ENNReal.ofReal (rho ^ 2 / 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr, integral_id]
      norm_num
    · exact ((continuous_id).integrableOn_Icc).mono_set Ioo_subset_Icc_self
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy using hy.1.le
  rw [hradial, ← ENNReal.ofReal_mul (by positivity)]
  ring_nf

end Math

import RequestProject.Wedge

open MeasureTheory Metric Set Real InnerProductGeometry
open scoped ENNReal RealInnerProductSpace Pointwise

namespace Math

/-! ## Definitions -/

/-- The (surface) area of a subset `S` of the unit sphere of `ℝ³`, defined as three times
the Lebesgue measure of the solid cone `{t • x : 0 < t < 1, x ∈ S}` that it subtends.
This is the standard surface measure; see `Math.sphericalArea_eq_toSphere`. -/
