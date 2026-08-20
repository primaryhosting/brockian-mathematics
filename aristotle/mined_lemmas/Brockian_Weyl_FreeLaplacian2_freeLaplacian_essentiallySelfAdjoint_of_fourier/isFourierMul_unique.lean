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

/-
# Free Laplacian Essentially Self Adjoint Of Fourier
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Free Laplacian Essentially Self Adjoint Of Fourier
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open MeasureTheory SchwartzMap FourierTransform Laplacian LineDeriv

noncomputable section

namespace Brockian.Weyl.FreeLaplacian2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The complex Hilbert space `L²(E)` of square integrable functions on a finite-dimensional
real inner product space `E`, with respect to the Lebesgue (Haar) measure. -/
abbrev L2Space (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] : Type _ := ↥(Lp (α := E) ℂ 2 volume)

/-- Schwartz functions viewed as elements of `L²(E)`. -/

theorem isFourierMul_unique {y w₁ w₂ : L2Space E} (h₁ : IsFourierMul y w₁)
    (h₂ : IsFourierMul y w₂) : w₁ = w₂ := by
  have hae : (fun ξ => ((𝓕 w₁ : L2Space E) ξ)) =ᵐ[volume] fun ξ => ((𝓕 w₂ : L2Space E) ξ) := by
    filter_upwards [h₁, h₂] with ξ e₁ e₂
    rw [← e₁, ← e₂]
  have hFeq : (𝓕 w₁ : L2Space E) = (𝓕 w₂ : L2Space E) := by
    exact Lp.ext hae
  calc w₁ = 𝓕⁻ (𝓕 w₁ : L2Space E) := (FourierTransform.fourierInv_fourier_eq w₁).symm
    _ = 𝓕⁻ (𝓕 w₂ : L2Space E) := by rw [hFeq]
    _ = w₂ := FourierTransform.fourierInv_fourier_eq w₂

