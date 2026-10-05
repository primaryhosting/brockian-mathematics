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

lemma integral_right_half (c : ℂ) (hc : c ≠ 0) :
    ∫ v in (0:ℝ)..1, (1 - (v:ℂ)) * Complex.exp (c * v)
      = Complex.exp c / c ^ 2 - 1 / c - 1 / c ^ 2 := by
  have key : ∀ x : ℝ, HasDerivAt (fun x : ℝ => (1 - (x:ℂ)) * Complex.exp (c * x) / c
      + Complex.exp (c * x) / c ^ 2) ((1 - (x:ℂ)) * Complex.exp (c * x)) x := by
    intro x
    have he := hasDerivAt_cexp_mul c x
    have h2 : HasDerivAt (fun x : ℝ => (1 - (x:ℂ))) (-1) x := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := x)).const_sub 1)
    have := ((h2.mul he).div_const c).add (he.div_const (c ^ 2))
    convert this using 1
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => key x)]
  · push_cast
    field_simp
    norm_num
    ring
  · exact (Continuous.intervalIntegrable (by fun_prop) _ _)

