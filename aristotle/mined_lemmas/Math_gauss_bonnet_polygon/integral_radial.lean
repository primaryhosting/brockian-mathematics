import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma integral_radial : ∫ r in (0:ℝ)..1, 2 * r * √(1 - r ^ 2) = 2 / 3 := by
  have hcont : ContinuousOn (fun r : ℝ => -2 / 3 * ((1 - r ^ 2) * √(1 - r ^ 2))) (Icc 0 1) := by
    fun_prop
  have hderiv : ∀ r ∈ Ioo (0:ℝ) 1,
      HasDerivAt (fun r : ℝ => -2 / 3 * ((1 - r ^ 2) * √(1 - r ^ 2))) (2 * r * √(1 - r ^ 2)) r := by
    intro r hr
    have hpos : (0:ℝ) < 1 - r ^ 2 := by nlinarith [hr.1, hr.2]
    have h1 : (1 : ℝ) - r ^ 2 ≠ 0 := ne_of_gt hpos
    have hsq : √(1 - r ^ 2) ^ 2 = 1 - r ^ 2 := Real.sq_sqrt hpos.le
    have hne : √(1 - r ^ 2) ≠ 0 := by positivity
    have hg : HasDerivAt (fun r : ℝ => 1 - r ^ 2) (-(2 * r)) r := by
      simpa using ((hasDerivAt_pow 2 r).const_sub 1)
    have hs : HasDerivAt (fun r : ℝ => √(1 - r ^ 2)) (1 / (2 * √(1 - r ^ 2)) * -(2 * r)) r :=
      (Real.hasDerivAt_sqrt h1).comp r hg
    have hmul : HasDerivAt (fun r : ℝ => (1 - r ^ 2) * √(1 - r ^ 2))
        (-(2 * r) * √(1 - r ^ 2) + (1 - r ^ 2) * (1 / (2 * √(1 - r ^ 2)) * -(2 * r))) r :=
      hg.mul hs
    have key : ∀ s : ℝ, s ≠ 0 → s ^ 2 = 1 - r ^ 2 →
        -2 / 3 * (-(2 * r) * s + (1 - r ^ 2) * (1 / (2 * s) * -(2 * r))) = 2 * r * s := by
      intro s hs0 hs2
      rw [← hs2]
      field_simp
      ring
    exact (hmul.const_mul (-2 / 3 : ℝ)).congr_deriv (key _ hne hsq)
  have hint : IntervalIntegrable (fun r : ℝ => 2 * r * √(1 - r ^ 2)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (by norm_num) hcont
    (fun r hr => (hderiv r hr).hasDerivWithinAt) hint]
  norm_num

