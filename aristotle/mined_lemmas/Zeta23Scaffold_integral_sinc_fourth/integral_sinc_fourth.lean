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

theorem integral_sinc_fourth : ∫ x : ℝ, (Real.sin x / x) ^ 4 = 2 * Real.pi / 3 := by
  rw [← integral_sinc_pow_four]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [ae_ne_zero] with x hx
  rw [Real.sinc_of_ne_zero hx]

end Zeta23Scaffold

