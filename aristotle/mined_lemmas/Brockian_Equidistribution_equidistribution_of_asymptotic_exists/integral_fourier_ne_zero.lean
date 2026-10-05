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
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

open Filter Topology MeasureTheory Complex

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Brockian.Equidistribution

/-! ## Weyl averages of continuous functions on the circle -/

/-- The `N`-th Weyl average of a continuous function `f` on the circle `ℝ / ℤ`, sampled along the
orbit `n ↦ n • α` of the rotation by `α`. -/

theorem integral_fourier_ne_zero {k : ℤ} (hk : k ≠ 0) :
    ∫ x : AddCircle (1 : ℝ), fourier k x = 0 := by
  have hc : (2 * (Real.pi : ℂ) * I * (k : ℂ)) ≠ 0 := by simp [Real.pi_ne_zero, hk]
  have hfun : ∀ x : ℝ, fourier k ((x : ℝ) : AddCircle (1 : ℝ))
      = Complex.exp ((2 * (Real.pi : ℂ) * I * (k : ℂ)) * x) := by
    intro x
    rw [fourier_coe_apply]
    norm_num
  rw [← AddCircle.integral_preimage (1 : ℝ) 0, ← intervalIntegral.integral_of_le (by norm_num),
    intervalIntegral.integral_congr
      (g := fun x : ℝ => Complex.exp ((2 * (Real.pi : ℂ) * I * (k : ℂ)) * x))
      fun x _ => hfun x,
    integral_exp_mul_complex hc]
  have h : (2 * (Real.pi : ℂ) * I * (k : ℂ)) * ((0 : ℝ) + 1 : ℝ) = (k : ℂ) * (2 * Real.pi * I) := by
    push_cast; ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]
  simp

