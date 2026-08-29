import Mathlib

/-!
# Integral Sinc Fourth
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_fourth
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

set_option grind.warning false

namespace Zeta23Scaffold

open MeasureTheory Real FourierTransform intervalIntegral

/-! ## The tent function and its Fourier transform -/

/-- The tent (triangle) function, supported on `[-1, 1]`. -/

lemma integral_fourier_mul {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ : ℝ, (𝓕 f ξ) * (g ξ) = ∫ x : ℝ, f x * 𝓕 g x := by
  have hflip : (innerₗ ℝ).flip = (innerₗ ℝ) := by ext; simp
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ)) (L := innerₗ ℝ) (e := 𝐞) (f := f) (g := g)
    Real.continuous_fourierChar (by fun_prop) hf hg
  rw [hflip] at h
  simpa [smul_eq_mul] using h

/-- Fourier inversion, in the form `𝓕 (𝓕 f) x = f (-x)`. -/
