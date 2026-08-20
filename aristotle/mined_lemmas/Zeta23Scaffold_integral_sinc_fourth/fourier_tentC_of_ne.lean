/-
# Integral Sinc Fourth
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_fourth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Integral Sinc Fourth
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_fourth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

We prove `∫ x : ℝ, (sin x / x) ^ 4 = 2 * π / 3`.

The argument is the classical Fourier-analytic one.  Let `tent` be the triangle function
`t ↦ max (1 - |t|) 0`.  Its Fourier transform is `ξ ↦ sinc (π ξ) ^ 2`.  The multiplication
(Parseval) formula `∫ 𝓕 f * g = ∫ f * 𝓕 g`, applied with `f = tent` and `g = 𝓕 tent`,
together with Fourier inversion (`𝓕 (𝓕 tent) = tent ∘ neg`), gives

`∫ sinc (π ξ) ^ 4 dξ = ∫ tent ^ 2 = 2 / 3`,

and a change of variables `x = π ξ` yields the result.
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

open MeasureTheory FourierTransform Real Complex

/-- The tent (triangle) function, supported on `[-1, 1]`. -/

lemma fourier_tentC_of_ne {ξ : ℝ} (hξ : ξ ≠ 0) : 𝓕 tentC ξ = sincSq ξ := by
  set c : ℂ := -(2 * π * ξ) * I with hcdef
  have hc : c ≠ 0 := by
    rw [hcdef]
    simp [Complex.I_ne_zero, Real.pi_ne_zero, hξ]
  have hstep : 𝓕 tentC ξ = ∫ t : ℝ, Complex.exp (c * t) * tentC t := by
    rw [Real.fourier_eq']
    congr 1
    funext t
    congr 1
    · congr 1
      rw [hcdef]
      push_cast
      simp
      ring
  rw [hstep, integral_mul_tentC (g := fun t : ℝ => Complex.exp (c * t))
      (Complex.continuous_exp.comp (by fun_prop)),
    integral_cexp_mul_linear c hc, integral_cexp_mul_linear c hc]
  have hcollect :
      (Complex.exp (c * ((0 : ℝ) : ℂ)) * (((1 : ℂ) - 1 / c) / c + (1 / c) * ((0 : ℝ) : ℂ)) -
        Complex.exp (c * ((-1 : ℝ) : ℂ)) * (((1 : ℂ) - 1 / c) / c + (1 / c) * ((-1 : ℝ) : ℂ))) +
      (Complex.exp (c * ((1 : ℝ) : ℂ)) * (((1 : ℂ) - (-1) / c) / c + ((-1) / c) * ((1 : ℝ) : ℂ)) -
        Complex.exp (c * ((0 : ℝ) : ℂ)) * (((1 : ℂ) - (-1) / c) / c + ((-1) / c) * ((0 : ℝ) : ℂ)))
      = (Complex.exp c + Complex.exp (-c) - 2) / c ^ 2 := by
    push_cast
    simp only [mul_zero, mul_one, Complex.exp_zero]
    field_simp
    ring
  rw [hcollect, hcdef]
  -- final trigonometric identity
  have hpx : π * ξ ≠ 0 := mul_ne_zero Real.pi_ne_zero hξ
  have hcos : Complex.exp (-(2 * π * ξ) * I) + Complex.exp (-(-(2 * π * ξ) * I))
      = 2 * Complex.cos ((2 * π * ξ : ℝ) : ℂ) := by
    rw [Complex.two_cos]
    push_cast
    ring_nf
  rw [hcos, ← Complex.ofReal_cos]
  have hI : ((-(2 * π * ξ) * I)) ^ 2 = ((-(2 * π * ξ) ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [mul_pow, Complex.I_sq]
    ring
  rw [hI, sincSq, Real.sinc_of_ne_zero hpx, ← Complex.ofReal_ofNat 2, ← Complex.ofReal_mul,
    ← Complex.ofReal_sub, ← Complex.ofReal_div]
  norm_cast
  have h2 : Real.cos (2 * π * ξ) = 1 - 2 * Real.sin (π * ξ) ^ 2 := by
    have h : (2 : ℝ) * π * ξ = 2 * (π * ξ) := by ring
    rw [h, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (π * ξ)]
  rw [h2]
  field_simp
  ring

