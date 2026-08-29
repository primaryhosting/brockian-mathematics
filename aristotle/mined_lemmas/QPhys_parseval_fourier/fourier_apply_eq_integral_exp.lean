/-
# Parseval Fourier
Category: Quantum Physics
Target: QPhys.parseval_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QPhys

open SchwartzMap MeasureTheory FourierTransform

/-- The Fourier transform of a function `f : ℝ → ℂ`, written out explicitly as the integral
`∫ x, e^{-2πi x ξ} f x`, agrees with Mathlib's Fourier transform `𝓕`. -/

theorem fourier_apply_eq_integral_exp (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 f ξ = ∫ x : ℝ, Complex.exp ((-2 * Real.pi * x * ξ) * Complex.I) * f x := by
  rw [Real.fourier_eq]
  congr 1 with x
  rw [Circle.smul_def]
  simp only [Real.fourierChar_apply, smul_eq_mul, RCLike.inner_apply, conj_trivial]
  congr 2
  push_cast
  ring

/-- **Parseval/Plancherel theorem for the Fourier transform.**

For a (Schwartz-class) quantum-mechanical wave function `psi : ℝ → ℂ`, the position-space
probability density `‖psi x‖²` and the momentum-space probability density `‖psi̅(ξ)‖²`, where
`psi̅(ξ) = ∫ e^{-2πi x ξ} psi x dx` is the Fourier transform, have the same total mass:
the Fourier transform is an `L²`-isometry. -/
