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
