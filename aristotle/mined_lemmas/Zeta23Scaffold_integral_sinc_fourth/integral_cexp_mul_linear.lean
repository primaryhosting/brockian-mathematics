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

lemma integral_cexp_mul_linear (c : ℂ) (hc : c ≠ 0) (A B : ℂ) (u v : ℝ) :
    ∫ t in u..v, Complex.exp (c * t) * (A + B * t) =
      Complex.exp (c * v) * ((A - B / c) / c + (B / c) * v) -
        Complex.exp (c * u) * ((A - B / c) / c + (B / c) * u) := by
  have hcp : c * ((A - B / c) / c) + B / c = A := by field_simp; ring
  have hcq : c * (B / c) = B := by field_simp
  have hd : ∀ t : ℝ, HasDerivAt
      (fun s : ℝ => Complex.exp (c * s) * ((A - B / c) / c + (B / c) * s))
      (Complex.exp (c * t) * (A + B * t)) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
      simpa using Complex.ofRealCLM.hasDerivAt (x := t)
    have h2 : HasDerivAt (fun s : ℝ => Complex.exp (c * s)) (Complex.exp (c * t) * (c * 1)) t :=
      (h1.const_mul c).cexp
    have h3 : HasDerivAt (fun s : ℝ => (A - B / c) / c + (B / c) * (s : ℂ)) ((B / c) * 1) t :=
      (h1.const_mul (B / c)).const_add _
    refine (h2.mul h3).congr_deriv ?_
    calc Complex.exp (c * t) * (c * 1) * ((A - B / c) / c + (B / c) * t)
            + Complex.exp (c * t) * ((B / c) * 1)
        = Complex.exp (c * t) * ((c * ((A - B / c) / c) + B / c) + (c * (B / c)) * t) := by ring
      _ = Complex.exp (c * t) * (A + B * t) := by rw [hcp, hcq]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (Continuous.intervalIntegrable (by fun_prop) _ _)

/-- The Fourier transform of the tent function at a nonzero point. -/
