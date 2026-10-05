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

lemma integral_sinc_pow_four : ∫ x : ℝ, Real.sinc x ^ 4 = 2 * π / 3 := by
  have h := MeasureTheory.Measure.integral_comp_mul_left (fun u : ℝ => Real.sinc u ^ 4) π
  rw [integral_sincSq_sq] at h
  rw [abs_of_pos (inv_pos.2 Real.pi_pos), smul_eq_mul] at h
  field_simp at h
  linarith [h, Real.pi_pos]

/-- `∫_ℝ (sin x / x)^4 dx = 2π/3`. -/
