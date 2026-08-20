import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma lintegral_sector (ψ : ℝ) (h0 : 0 < ψ) (hπ : ψ < π) :
    ∫⁻ p in {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ cos ψ * p.1 + sin ψ * p.2},
        ENNReal.ofReal (2 * √(1 - p.1 ^ 2 - p.2 ^ 2))
      = ENNReal.ofReal (2 * (π - ψ) / 3) := by
  set D : Set (ℝ × ℝ) := {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ cos ψ * p.1 + sin ψ * p.2} with hDdef
  set T : Set ℝ := Icc (ψ - π / 2) (π / 2) with hTdef
  have hDmeas : MeasurableSet D := by
    apply MeasurableSet.inter
    · exact measurableSet_le measurable_const measurable_fst
    · exact measurableSet_le measurable_const
        ((measurable_const.mul measurable_fst).add (measurable_const.mul measurable_snd))
  rw [← lintegral_indicator hDmeas, ← lintegral_comp_polarCoord_symm]
  have hstep : ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 •
        D.indicator (fun p : ℝ × ℝ => ENNReal.ofReal (2 * √(1 - p.1 ^ 2 - p.2 ^ 2)))
          (polarCoord.symm p)
      = ∫⁻ p in polarCoord.target,
          (Ioi (0:ℝ) ×ˢ T).indicator (fun p : ℝ × ℝ =>
            ENNReal.ofReal (2 * p.1 * √(1 - p.1 ^ 2))) p := by
    refine setLIntegral_congr_fun polarCoord.open_target.measurableSet ?_
    rintro ⟨r, theta⟩ hp
    rw [polarCoord_target] at hp
    obtain ⟨hr, hθ⟩ := hp
    simp only [mem_Ioi] at hr
    simp only [polarCoord_symm_apply, smul_eq_mul]
    have hcos : (r * cos theta) ^ 2 + (r * sin theta) ^ 2 = r ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq theta]
    have hmem : ((r * cos theta, r * sin theta) ∈ D) ↔ (r, theta) ∈ Ioi (0:ℝ) ×ˢ T := by
      simp only [hDdef, mem_setOf_eq, Set.mem_prod, mem_Ioi, hr, true_and]
      rw [← sector_theta ψ theta h0 hπ hθ]
      constructor
      · rintro ⟨h1, h2⟩
        have h1' : 0 ≤ cos theta * r := by rw [mul_comm]; exact h1
        refine ⟨nonneg_of_mul_nonneg_left h1' hr, ?_⟩
        have h2' : 0 ≤ (cos ψ * cos theta + sin ψ * sin theta) * r := by nlinarith [h2]
        exact nonneg_of_mul_nonneg_left h2' hr
      · rintro ⟨h1, h2⟩
        exact ⟨by positivity, by nlinarith [h2]⟩
    by_cases hin : (r, theta) ∈ Ioi (0:ℝ) ×ˢ T
    · rw [Set.indicator_of_mem hin, Set.indicator_of_mem (hmem.mpr hin)]
      rw [show (1 : ℝ) - (r * cos theta) ^ 2 - (r * sin theta) ^ 2 = 1 - r ^ 2 by nlinarith [hcos]]
      rw [← ENNReal.ofReal_mul hr.le]
      congr 1
      ring
    · rw [Set.indicator_of_notMem hin, Set.indicator_of_notMem (fun h => hin (hmem.mp h))]
      simp
  rw [hstep]
  have hsub : Ioi (0:ℝ) ×ˢ T ⊆ polarCoord.target := by
    rw [polarCoord_target]
    rintro ⟨r, theta⟩ ⟨hr, hθ⟩
    refine ⟨hr, ?_⟩
    simp only [hTdef, mem_Icc] at hθ
    exact ⟨by linarith [Real.pi_pos, hθ.1], by linarith [Real.pi_pos, hθ.2]⟩
  have hTmeas : MeasurableSet (Ioi (0:ℝ) ×ˢ T) := measurableSet_Ioi.prod measurableSet_Icc
  rw [lintegral_indicator hTmeas, Measure.restrict_restrict hTmeas, inter_eq_left.mpr hsub,
    lintegral_prod_fst (fun r => ENNReal.ofReal (2 * r * √(1 - r ^ 2))) (by fun_prop)
      (Ioi (0:ℝ)) T, lintegral_radial, hTdef, Real.volume_Icc,
    ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

/-- The volume of the standard wedge of the unit ball with dihedral angle `π - ψ`. -/
