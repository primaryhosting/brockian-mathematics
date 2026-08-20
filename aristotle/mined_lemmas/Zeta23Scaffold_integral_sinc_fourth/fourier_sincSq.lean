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

lemma fourier_sincSq (x : ℝ) : 𝓕 sincSq x = tentC (-x) := by
  have hinv : 𝓕⁻ (𝓕 tentC) = tentC :=
    Continuous.fourierInv_fourier_eq continuous_tentC integrable_tentC
      (by rw [fourier_tentC]; exact integrable_sincSq)
  have h := Real.fourierInv_eq_fourier_neg (𝓕 tentC) (-x)
  rw [hinv] at h
  rw [← fourier_tentC]
  simpa using h.symm

/-- The multiplication (Parseval) formula for integrable functions on `ℝ`. -/
