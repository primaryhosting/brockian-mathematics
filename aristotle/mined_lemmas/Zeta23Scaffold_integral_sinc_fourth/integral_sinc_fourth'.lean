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

open MeasureTheory Real FourierTransform Complex

namespace Zeta23Scaffold

/-! ## The tent function -/

/-- The tent (triangle) function, supported on `[-1, 1]`. -/

lemma integral_sinc_fourth' : ∫ x : ℝ, (Real.sinc x)^4 = 2 * π / 3 := by
  have h := Measure.integral_comp_mul_left (fun x : ℝ => (Real.sinc x)^4) π
  rw [integral_sinc_pi_fourth] at h
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ π⁻¹), smul_eq_mul] at h
  have hπ : (π:ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp at h
  linarith [h]

