/-
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The normalization integral of the sine kernel,
`∫ x : ℝ, (sin x / x) ^ 2 = π`.

The proof computes the Fourier transform of the triangle function
`tri x = max (1 - |x|) 0`, which is `w ↦ sinc (π w) ^ 2`, and then applies the
Fourier inversion formula at `0`.

Note that in Lean `sin 0 / 0 = 0`, so the integrand of the main statement differs from the
continuous extension `sinc` only on the null set `{0}`; the value of the integral is unaffected.
-/

open MeasureTheory Real Complex
open scoped FourierTransform

namespace Zeta23Scaffold

/-- The triangle function `x ↦ max (1 - |x|) 0`, viewed as a complex-valued function on `ℝ`. -/

theorem integral_sinc_sq : ∫ x : ℝ, (Real.sin x / x) ^ 2 = π := by
  have hae : (fun x : ℝ => (Real.sin x / x) ^ 2) =ᵐ[volume] fun x : ℝ => Real.sinc x ^ 2 := by
    have h0 : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [h0] with x hx
    rw [Real.sinc_of_ne_zero hx]
  rw [MeasureTheory.integral_congr_ae hae]
  have hchange : ∫ w : ℝ, Real.sinc (π * w) ^ 2 = |π⁻¹| • ∫ x : ℝ, Real.sinc x ^ 2 :=
    MeasureTheory.Measure.integral_comp_mul_left (fun x => Real.sinc x ^ 2) π
  rw [integral_sinc_pi_mul_sq, abs_of_pos (by positivity : (0:ℝ) < π⁻¹), smul_eq_mul] at hchange
  field_simp at hchange
  linarith

end Zeta23Scaffold

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

