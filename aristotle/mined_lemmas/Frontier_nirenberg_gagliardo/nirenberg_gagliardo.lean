import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open MeasureTheory

/-- Cauchy–Schwarz for the Lebesgue integral on `ℝ`: for continuous, compactly supported
`u, v : ℝ → ℝ` we have `∫ |u| |v| ≤ √(∫ u²) * √(∫ v²)`. -/

theorem nirenberg_gagliardo {f f' : ℝ → ℝ} (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf'c : Continuous f') (hsupp : HasCompactSupport f) (x : ℝ) :
    f x ^ 2 ≤ 2 * Real.sqrt (∫ t : ℝ, f t ^ 2) * Real.sqrt (∫ t : ℝ, f' t ^ 2) := by
  have hf : Continuous f := continuous_iff_continuousAt.2 fun t => (hderiv t).continuousAt
  have hsupp' : HasCompactSupport f' := hasCompactSupport_of_hasDerivAt hderiv hsupp
  obtain ⟨a, hax, hfa⟩ := exists_le_eq_zero_of_hasCompactSupport hsupp x
  have hcont2 : Continuous fun t : ℝ => 2 * f t * f' t := by fun_prop
  have hcontabs : Continuous fun t : ℝ => 2 * (|f t| * |f' t|) := by fun_prop
  have hsuppabs : HasCompactSupport fun t : ℝ => 2 * (|f t| * |f' t|) := by
    apply HasCompactSupport.mul_left
    exact (hsupp.abs).mul_right
  have key : (∫ t in a..x, 2 * f t * f' t) = f x ^ 2 - f a ^ 2 := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => f t ^ 2)
      (fun t _ => ?_) (hcont2.intervalIntegrable _ _)
    simpa [mul_comm] using (hderiv t).pow 2
  have h1 : (∫ t in a..x, 2 * f t * f' t) ≤ ∫ t in a..x, 2 * (|f t| * |f' t|) := by
    refine intervalIntegral.integral_mono_on hax (hcont2.intervalIntegrable _ _)
      (hcontabs.intervalIntegrable _ _) (fun t _ => ?_)
    rw [mul_assoc]
    have : f t * f' t ≤ |f t| * |f' t| := by
      calc f t * f' t ≤ |f t * f' t| := le_abs_self _
        _ = |f t| * |f' t| := abs_mul _ _
    linarith
  have h2 : (∫ t in a..x, 2 * (|f t| * |f' t|)) ≤ ∫ t : ℝ, 2 * (|f t| * |f' t|) := by
    rw [intervalIntegral.integral_of_le hax]
    refine setIntegral_le_integral (hcontabs.integrable_of_hasCompactSupport hsuppabs) ?_
    filter_upwards with t
    positivity
  have h3 : (∫ t : ℝ, 2 * (|f t| * |f' t|)) = 2 * ∫ t : ℝ, |f t| * |f' t| := by
    rw [integral_const_mul]
  have h4 : (∫ t : ℝ, |f t| * |f' t|)
      ≤ Real.sqrt (∫ t : ℝ, f t ^ 2) * Real.sqrt (∫ t : ℝ, f' t ^ 2) :=
    integral_abs_mul_le_sqrt_mul_sqrt hf hf'c hsupp hsupp'
  have hfa2 : f a ^ 2 = 0 := by rw [hfa]; ring
  nlinarith [h1, h2, h3, h4, key, hfa2]

/-- **Gagliardo–Nirenberg interpolation inequality**, one-dimensional base case, in the usual
multiplicative form: for a compactly supported, continuously differentiable `f : ℝ → ℝ`,
`‖f‖_∞ ≤ √2 · ‖f‖_{L²}^{1/2} · ‖f'‖_{L²}^{1/2}`. -/
