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

theorem exists_mem_adjoint_domain {u : E → ℂ} (hu : MemLp u 2 volume)
    (hmu : MemLp (fun ξ => (multiplier ξ : ℂ) * u ξ) 2 volume) :
    ∃ Y : (freeLaplacian (E := E)).adjoint.domain,
      (fun ξ => ((𝓕 (Y : L2Space E) : L2Space E) ξ)) =ᵐ[volume] u ∧
      (fun ξ => ((𝓕 ((freeLaplacian (E := E)).adjoint Y) : L2Space E) ξ)) =ᵐ[volume]
        fun ξ => (multiplier ξ : ℂ) * u ξ := by
  set Y : L2Space E := 𝓕⁻ (hu.toLp u) with hYdef
  have hFY : (𝓕 Y : L2Space E) = hu.toLp u := FourierTransform.fourier_fourierInv_eq _
  have hY1 : (fun ξ => ((𝓕 Y : L2Space E) ξ)) =ᵐ[volume] u := by
    rw [hFY]; exact hu.coeFn_toLp
  have hmem : Y ∈ (freeLaplacian (E := E)).adjoint.domain := by
    refine (mem_adjoint_domain_iff Y).mpr ⟨𝓕⁻ (hmu.toLp _), ?_⟩
    have hFw : (𝓕 (𝓕⁻ (hmu.toLp (fun ξ => (multiplier ξ : ℂ) * u ξ)) : L2Space E) : L2Space E)
        = hmu.toLp _ := FourierTransform.fourier_fourierInv_eq _
    unfold IsFourierMul
    rw [hFw]
    filter_upwards [hY1, hmu.coeFn_toLp] with ξ h1 h2
    rw [h1, h2]
  refine ⟨⟨Y, hmem⟩, hY1, ?_⟩
  have h := isFourierMul_adjoint (E := E) ⟨Y, hmem⟩
  unfold IsFourierMul at h
  filter_upwards [h, hY1] with ξ h1 h2
  rw [← h1, h2]

/-- The crucial step: if `w` represents the pairing of `z` against the whole adjoint operator,
then `w` is the multiplier applied to `z` on the Fourier side. -/
