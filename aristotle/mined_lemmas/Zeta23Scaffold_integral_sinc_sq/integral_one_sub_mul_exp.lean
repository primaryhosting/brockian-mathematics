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

The Dirichlet-type integral `∫_ℝ (sin x / x)^2 dx = π`.

The proof goes through the Fourier inversion formula applied to the triangle function
`tri ξ = max (1 - |ξ|) 0`, whose Fourier transform is `x ↦ sinc (π x)^2`.
-/

open MeasureTheory Real intervalIntegral
open scoped FourierTransform RealInnerProductSpace

namespace Zeta23Scaffold

/-- The triangle function `ξ ↦ max (1 - |ξ|) 0`, viewed as a complex-valued function. -/

lemma integral_one_sub_mul_exp {a : ℂ} (ha : a ≠ 0) :
    (∫ ξ in (0:ℝ)..1, (1 - (ξ:ℂ)) * Complex.exp (a * ξ)) =
      (Complex.exp a - a - 1) / a ^ 2 := by
  have key : ∀ ξ ∈ Set.uIcc (0:ℝ) 1, HasDerivAt
      (fun t : ℝ => (1 - (t:ℂ)) * Complex.exp (a * t) / a + Complex.exp (a * t) / a ^ 2)
      ((1 - (ξ:ℂ)) * Complex.exp (a * ξ)) ξ := by
    intro ξ _
    have h1 : HasDerivAt (fun t : ℝ => (t:ℂ)) 1 ξ := Complex.ofRealCLM.hasDerivAt
    have h2 : HasDerivAt (fun t : ℝ => Complex.exp (a * t)) (a * Complex.exp (a * ξ)) ξ := by
      have := (Complex.hasDerivAt_exp (a * ξ)).comp ξ (h1.const_mul a)
      simpa [mul_comm] using this
    have h3 : HasDerivAt (fun t : ℝ => (1 - (t:ℂ)) * Complex.exp (a * t))
        (-1 * Complex.exp (a * ξ) + (1 - (ξ:ℂ)) * (a * Complex.exp (a * ξ))) ξ :=
      ((h1.const_sub 1).mul h2)
    have := (h3.div_const a).add (h2.div_const (a ^ 2))
    convert this using 1
    field_simp
    ring
  rw [integral_eq_sub_of_hasDerivAt key]
  · push_cast
    simp only [mul_zero, Complex.exp_zero]
    field_simp
    ring
  · apply Continuous.intervalIntegrable
    fun_prop

/-- Antiderivative computation: `∫_{-1}^0 (1 + ξ) e^{aξ} dξ = (a - 1 + e^{-a})/a^2`. -/
