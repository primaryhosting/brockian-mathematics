import RequestProject.Sector

open MeasureTheory Metric Set Real InnerProductGeometry
open scoped ENNReal RealInnerProductSpace

namespace Math

/-- Euclidean three-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The volume of the standard solid wedge of dihedral angle `psi` inside the unit ball:
the axis of the wedge is the first coordinate axis, and the wedge is described in the plane
of the last two coordinates as the cone spanned by `(1,0)` and `(cos psi, sin psi)`. -/

theorem volume_wedge_std (psi : ℝ) (h0 : 0 ≤ psi) (hpi : psi ≤ π) :
    volume {y : E3 | ‖y‖ < 1 ∧ 0 ≤ y 2 ∧ 0 ≤ y 1 * Real.sin psi - y 2 * Real.cos psi}
      = ENNReal.ofReal (2 * psi / 3) := by
  set S : Set E3 := {y : E3 | ‖y‖ < 1 ∧ 0 ≤ y 2 ∧ 0 ≤ y 1 * Real.sin psi - y 2 * Real.cos psi}
    with hSdef
  set W : Set (ℝ × (Fin 2 → ℝ)) := {p | p.1 ^ 2 + (p.2 0) ^ 2 + (p.2 1) ^ 2 < 1 ∧ 0 ≤ p.2 1 ∧
      0 ≤ p.2 0 * Real.sin psi - p.2 1 * Real.cos psi} with hWdef
  have hSm : MeasurableSet S := by rw [hSdef]; measurability
  have hWm : MeasurableSet W := by rw [hWdef]; measurability
  -- transfer the problem to `ℝ × (Fin 2 → ℝ)`, splitting off the axis coordinate
  have h1 : volume S = volume ((WithLp.toLp 2 : (Fin 3 → ℝ) → E3) ⁻¹' S) :=
    ((PiLp.volume_preserving_toLp (Fin 3)).measure_preimage hSm.nullMeasurableSet).symm
  have h2 : ((WithLp.toLp 2 : (Fin 3 → ℝ) → E3) ⁻¹' S)
      = (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0) ⁻¹' W := by
    ext y
    have hnorm : ‖(WithLp.toLp 2 y : E3)‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      simp [Fin.sum_univ_three]
    have hlt : ‖(WithLp.toLp 2 y : E3)‖ < 1 ↔ y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 < 1 := by
      constructor
      · intro hh; nlinarith [norm_nonneg (WithLp.toLp 2 y : E3)]
      · intro hh; nlinarith [norm_nonneg (WithLp.toLp 2 y : E3)]
    simp only [mem_preimage, hSdef, hWdef, mem_setOf_eq, hlt]
    rfl
  have h3 : volume ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0) ⁻¹' W) = volume W :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).measure_preimage
      hWm.nullMeasurableSet
  -- each horizontal slice is a circular sector
  have hslice : ∀ t : ℝ, volume (Prod.mk t ⁻¹' W) = ENNReal.ofReal (psi * (1 - t ^ 2) / 2) := by
    intro t
    rcases le_or_gt (t ^ 2) 1 with hle | hgt
    · have hrho : Real.sqrt (1 - t ^ 2) ^ 2 = 1 - t ^ 2 := Real.sq_sqrt (by linarith)
      have hset : Prod.mk t ⁻¹' W = (MeasurableEquiv.finTwoArrow) ⁻¹'
          {z : ℝ × ℝ | z.1 ^ 2 + z.2 ^ 2 < Real.sqrt (1 - t ^ 2) ^ 2 ∧ 0 ≤ z.2 ∧
            0 ≤ z.1 * Real.sin psi - z.2 * Real.cos psi} := by
        ext z
        show (t ^ 2 + (z 0) ^ 2 + (z 1) ^ 2 < 1 ∧ 0 ≤ z 1 ∧
            0 ≤ z 0 * Real.sin psi - z 1 * Real.cos psi) ↔
          ((z 0) ^ 2 + (z 1) ^ 2 < Real.sqrt (1 - t ^ 2) ^ 2 ∧ 0 ≤ z 1 ∧
            0 ≤ z 0 * Real.sin psi - z 1 * Real.cos psi)
        rw [hrho]
        constructor
        · rintro ⟨ha, hb, hc⟩; exact ⟨by linarith, hb, hc⟩
        · rintro ⟨ha, hb, hc⟩; exact ⟨by linarith, hb, hc⟩
      rw [hset, (volume_preserving_finTwoArrow ℝ).measure_preimage (by measurability),
        volume_sector psi _ h0 hpi (Real.sqrt_nonneg _), hrho]
    · have hempty : Prod.mk t ⁻¹' W = ∅ := by
        ext z
        simp only [mem_preimage, hWdef, mem_setOf_eq, mem_empty_iff_false, iff_false]
        rintro ⟨ha, -, -⟩
        nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]
      rw [hempty, measure_empty, eq_comm, ENNReal.ofReal_eq_zero]
      have hneg : 1 - t ^ 2 ≤ 0 := by nlinarith
      have := mul_nonneg h0 (neg_nonneg.2 hneg)
      linarith
  rw [h1, h2, h3, Measure.volume_eq_prod, Measure.prod_apply hWm]
  simp only [hslice]
  -- integrate the slice areas
  have hfun : (fun t : ℝ => ENNReal.ofReal (psi * (1 - t ^ 2) / 2))
      = (Icc (-1 : ℝ) 1).indicator (fun t => ENNReal.ofReal (psi * (1 - t ^ 2) / 2)) := by
    funext t
    by_cases ht : t ∈ Icc (-1 : ℝ) 1
    · rw [Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht, ENNReal.ofReal_eq_zero]
      simp only [mem_Icc, not_and_or, not_le] at ht
      have hneg : 1 - t ^ 2 ≤ 0 := by rcases ht with hh | hh <;> nlinarith
      have := mul_nonneg h0 (neg_nonneg.2 hneg)
      linarith
  rw [hfun, lintegral_indicator measurableSet_Icc, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    congr 1
    simp [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, mul_sub]
    ring
  · apply Continuous.integrableOn_Icc; fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    simp only [mem_Icc] at hy
    show (0 : ℝ) ≤ psi * (1 - y ^ 2) / 2
    have hpos : 0 ≤ 1 - y ^ 2 := by nlinarith [hy.1, hy.2]
    have := mul_nonneg h0 hpos
    linarith

