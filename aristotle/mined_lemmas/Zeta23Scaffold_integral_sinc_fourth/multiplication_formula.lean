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

open MeasureTheory Real FourierTransform Complex

namespace Zeta23Scaffold

/-! ## The tent function -/

/-- The tent (triangle) function, supported on `[-1, 1]`. -/

lemma multiplication_formula (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ : ℝ, (𝓕 f ξ) * (g ξ) = ∫ x : ℝ, (f x) * (𝓕 g x) := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (V := ℝ) (W := ℝ)
    (L := (innerₗ ℝ)) (μ := volume) (ν := volume) (e := 𝐞) (f := f) (g := g)
    Real.continuous_fourierChar (by fun_prop) hf hg
  simpa [smul_eq_mul, Real.fourier_eq] using h

