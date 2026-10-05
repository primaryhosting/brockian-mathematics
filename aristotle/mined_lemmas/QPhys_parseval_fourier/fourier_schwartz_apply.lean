import Mathlib

/-!
# Parseval Fourier
Category: Quantum Physics
Target: QPhys.parseval_fourier
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QPhys

open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace

/-- The Fourier transform of a Schwartz function on `ℝ`, written out as an explicit
oscillatory integral with the physics normalisation `e^{-2πi x w}`. -/

theorem fourier_schwartz_apply (f : 𝓢(ℝ, ℂ)) (w : ℝ) :
    (𝓕 f) w = ∫ x : ℝ, Complex.exp ((-2 * π * x * w : ℝ) * Complex.I) * f x := by
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  simp [smul_eq_mul]

/-- **Parseval / Plancherel theorem for the Fourier transform.**

For a Schwartz function `f : ℝ → ℂ` (a wave function in the physics setting), the Fourier
transform, written explicitly with the kernel `e^{-2πi x w}`, preserves the `L²` norm:
the total probability computed in position space equals the one computed in momentum space. -/
