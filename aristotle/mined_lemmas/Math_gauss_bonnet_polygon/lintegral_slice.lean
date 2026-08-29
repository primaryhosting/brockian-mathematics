/-
Volume of a wedge of the unit ball of `EuclideanSpace ℝ (Fin 3)` in standard position.

This is an auxiliary file for the Gauss-Bonnet (Girard) theorem for spherical triangles.
-/
import RequestProject.Sector

open MeasureTheory Metric Set Real
open scoped ENNReal

namespace Math

/-- Euclidean 3-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The wedge of the unit ball cut out by the half-spaces with inner normals
`(1,0,0)` and `(cos t, sin t, 0)`. -/

private theorem lintegral_slice (c : ℝ) (hc : 0 ≤ c) :
    ∫⁻ z : ℝ, ENNReal.ofReal (c * (Real.sqrt (1 - z ^ 2)) ^ 2) = ENNReal.ofReal (c * (4 / 3)) := by
  have h1 : ∀ z : ℝ, ENNReal.ofReal (c * (Real.sqrt (1 - z ^ 2)) ^ 2)
      = (Icc (-1 : ℝ) 1).indicator (fun z => ENNReal.ofReal (c * (1 - z ^ 2))) z := by
    intro z
    by_cases hz : z ∈ Icc (-1 : ℝ) 1
    · rw [Set.indicator_of_mem hz]
      congr 2
      rw [Real.sq_sqrt]
      simp only [mem_Icc] at hz
      nlinarith [hz.1, hz.2]
    · rw [Set.indicator_of_notMem hz]
      simp only [mem_Icc, not_and_or, not_le] at hz
      have hzero : Real.sqrt (1 - z ^ 2) = 0 := by
        apply Real.sqrt_eq_zero_of_nonpos
        rcases hz with h | h <;> nlinarith
      rw [hzero]
      simp
  simp_rw [h1]
  rw [lintegral_indicator measurableSet_Icc, ← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num),
      intervalIntegral.integral_const_mul]
    norm_num [intervalIntegral.integral_sub, integral_pow, intervalIntegral.intervalIntegrable_pow]
  · exact (by fun_prop : Continuous fun z : ℝ => c * (1 - z ^ 2)).integrableOn_Icc
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
    simp only [mem_Icc] at hz
    have : (0 : ℝ) ≤ 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
    positivity

/-- **Volume of a wedge in standard position.**  For `0 ≤ t ≤ π`, the part of the unit ball of
`ℝ³` where both `x₀ > 0` and `x₀ cos t + x₁ sin t > 0` has volume `2 (π - t) / 3`.
Here `π - t` is the dihedral angle of the wedge. -/
