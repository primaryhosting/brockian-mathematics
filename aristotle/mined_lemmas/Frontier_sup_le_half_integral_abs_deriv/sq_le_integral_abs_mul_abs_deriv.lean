import Mathlib

/-!
# Nirenberg Gagliardo
Category: Frontier Abel
Target: Frontier.nirenberg_gagliardo
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- The `L^∞`–`W^{1,1}` endpoint estimate in dimension one: for a continuously
differentiable, compactly supported function `f : ℝ → ℝ` one has
`‖f‖_∞ ≤ (1/2) * ‖f'‖_1`. -/

theorem sq_le_integral_abs_mul_abs_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hsupp : HasCompactSupport f) (x : ℝ) :
    (f x) ^ 2 ≤ ∫ t : ℝ, |f t| * |deriv f t| := by
  have hderiv : ∀ y : ℝ, HasDerivAt f (deriv f y) y := fun y =>
    (hf.differentiable (by norm_num) y).hasDerivAt
  have hg : ContDiff ℝ 1 (fun t : ℝ => f t * f t) := hf.mul hf
  have hgs : HasCompactSupport (fun t : ℝ => f t * f t) := hsupp.mul_right
  have hd : ∀ t : ℝ, deriv (fun y : ℝ => f y * f y) t = 2 * (f t * deriv f t) := by
    intro t
    have h : HasDerivAt (fun y : ℝ => f y * f y) (deriv f t * f t + f t * deriv f t) t :=
      (hderiv t).mul (hderiv t)
    rw [h.deriv]; ring
  have habs : ∀ t : ℝ, |deriv (fun y : ℝ => f y * f y) t| = 2 * (|f t| * |deriv f t|) := by
    intro t
    rw [hd t, abs_mul, abs_mul]
    norm_num
  have key := sup_le_half_integral_abs_deriv hg hgs x
  rw [show |f x * f x| = (f x) ^ 2 by
    rw [abs_of_nonneg (mul_self_nonneg (f x))]; ring] at key
  have hint : (∫ t : ℝ, |deriv (fun y : ℝ => f y * f y) t|)
      = 2 * ∫ t : ℝ, |f t| * |deriv f t| := by
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall habs)
  rw [hint] at key
  linarith

/-- **Gagliardo–Nirenberg interpolation inequality**, base case in dimension one:
for a continuously differentiable, compactly supported `f : ℝ → ℝ`,
`‖f‖_∞ ^ 2 ≤ ‖f‖_2 * ‖f'‖_2`, i.e. `‖f‖_∞ ≤ ‖f‖_2 ^ (1/2) * ‖f'‖_2 ^ (1/2)`. -/
