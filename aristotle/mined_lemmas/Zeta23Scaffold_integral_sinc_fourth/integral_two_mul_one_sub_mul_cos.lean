import Mathlib

/-!
# Integral Sinc Fourth
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_fourth
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

set_option grind.warning false

namespace Zeta23Scaffold

open MeasureTheory Real FourierTransform intervalIntegral

/-! ## The tent function and its Fourier transform -/

/-- The tent (triangle) function, supported on `[-1, 1]`. -/

lemma integral_two_mul_one_sub_mul_cos (a : ℝ) (ha : a ≠ 0) :
    ∫ x in (0:ℝ)..1, 2 * (1 - x) * Real.cos (a * x) = 2 * (1 - Real.cos a) / a ^ 2 := by
  have key : ∀ x ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun y : ℝ => 2 * ((1 - y) * Real.sin (a * y) / a - Real.cos (a * y) / a ^ 2))
        (2 * (1 - x) * Real.cos (a * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => Real.sin (a * y)) (Real.cos (a * x) * a) x := by
      simpa using (Real.hasDerivAt_sin (a * x)).comp x ((hasDerivAt_id x).const_mul a)
    have h2 : HasDerivAt (fun y : ℝ => Real.cos (a * y)) (-Real.sin (a * x) * a) x := by
      simpa using (Real.hasDerivAt_cos (a * x)).comp x ((hasDerivAt_id x).const_mul a)
    have h3 : HasDerivAt (fun y : ℝ => (1 - y)) (-1 : ℝ) x := by
      simpa using (hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)
    have h4 := (((h3.mul h1).div_const a).sub (h2.div_const (a ^ 2))).const_mul (2:ℝ)
    convert h4 using 1
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt key
    ((by fun_prop : Continuous fun x : ℝ => 2 * (1 - x) * Real.cos (a * x)).intervalIntegrable _ _)]
  simp only [Real.sin_zero, Real.cos_zero, mul_zero, mul_one, sub_zero, sub_self, zero_mul,
    zero_div]
  field_simp
  ring

/-- The Fourier transform of the tent function is `sinc (π ξ) ^ 2`. -/
