import Mathlib
/-!
# Parseval Fourier
Category: Quantum Physics
Target: QPhys.parseval_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real ComplexConjugate
open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace

namespace QPhys

/-- The Fourier transform of a Schwartz function on `ℝ`, written out as an explicit integral
with the physics convention `e^{-2πi x ξ}`. -/
theorem fourier_apply_eq (f : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    𝓕 (f : ℝ → ℂ) ξ = ∫ x : ℝ, Complex.exp (-(2 * π * x * ξ) * Complex.I) * f x := by
  rw [Real.fourier_eq' (f : ℝ → ℂ) ξ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [RCLike.inner_apply, mul_comm, mul_assoc, mul_left_comm]

/-- **Parseval/Plancherel theorem for the Fourier transform.**

Two formulations:

* the `L²` statement: the Fourier transform on `L²(ℝ, ℂ)` is a norm-preserving (indeed,
  inner-product preserving) linear isometry;
* the concrete statement for Schwartz functions: with the physics normalisation
  `f̂(ξ) = ∫ f(x) e^{-2πi x ξ} dx`, the total "probability" `∫ |f|²` is unchanged by the
  Fourier transform. -/
theorem parseval_fourier :
    (∀ f g : Lp (α := ℝ) ℂ 2, ‖𝓕 f‖ = ‖f‖ ∧ ⟪𝓕 f, 𝓕 g⟫ = ⟪f, g⟫) ∧
    (∀ f : 𝓢(ℝ, ℂ),
      ∫ ξ : ℝ, ‖∫ x : ℝ, Complex.exp (-(2 * π * x * ξ) * Complex.I) * f x‖ ^ 2
        = ∫ x : ℝ, ‖f x‖ ^ 2) := by
  refine ⟨fun f g => ⟨Lp.norm_fourier_eq f, Lp.inner_fourier_eq f g⟩, fun f => ?_⟩
  have h : ∀ ξ : ℝ, (∫ x : ℝ, Complex.exp (-(2 * π * x * ξ) * Complex.I) * f x)
      = 𝓕 (f : ℝ → ℂ) ξ := fun ξ => (fourier_apply_eq f ξ).symm
  simp_rw [h]
  exact SchwartzMap.integral_norm_sq_fourier f

end QPhys

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

