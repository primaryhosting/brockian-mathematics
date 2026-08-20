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

private theorem lintegral_one_sub_sq (c : ℝ) (hc : 0 ≤ c) :
    ∫⁻ (z : ℝ), ENNReal.ofReal (c * (1 - z ^ 2)) = ENNReal.ofReal (c * (4 / 3)) := by
  rw [← lintegral_add_compl (μ := volume) (fun z => ENNReal.ofReal (c * (1 - z ^ 2)))
      (measurableSet_Icc (a := (-1 : ℝ)) (b := 1))]
  have h2 : ∫⁻ z in (Icc (-1 : ℝ) 1)ᶜ, ENNReal.ofReal (c * (1 - z ^ 2)) = 0 := by
    rw [setLIntegral_congr_fun measurableSet_Icc.compl
      (f := fun z => ENNReal.ofReal (c * (1 - z ^ 2))) (g := fun _ => 0) ?_, lintegral_zero]
    intro z hz
    simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at hz
    have : 1 - z ^ 2 ≤ 0 := by rcases hz with h | h <;> nlinarith
    simp only [ENNReal.ofReal_eq_zero]
    nlinarith
  rw [h2, add_zero, ← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_sub intervalIntegrable_const
        (intervalIntegral.intervalIntegrable_pow 2)]
    simp [integral_pow]
    norm_num
  · apply Integrable.mono' (g := fun _ => c * 1) (integrable_const _)
    · fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
      simp only [mem_Icc] at hz
      have h0 : (0 : ℝ) ≤ 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc h0)]
      nlinarith
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
    simp only [mem_Icc] at hz
    have h0 : (0 : ℝ) ≤ 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
    exact mul_nonneg hc h0

/-- The volume of the wedge in standard position: the intersection of the unit ball with the
half-spaces `0 ≤ x 0` and `0 ≤ cos θ * x 0 + sin θ * x 1`. -/
