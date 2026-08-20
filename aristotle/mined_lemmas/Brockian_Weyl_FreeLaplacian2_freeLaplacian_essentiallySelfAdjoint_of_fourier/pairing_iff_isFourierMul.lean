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

theorem pairing_iff_isFourierMul (y w : L2Space E) :
    (∀ f : 𝓢(E, ℂ), inner ℂ w (toL2 f) = inner ℂ y (toL2 (-(Δ f)))) ↔ IsFourierMul y w := by
  have hleft : ∀ f : 𝓢(E, ℂ), inner ℂ w (toL2 f)
      = ∫ ξ, (starRingEnd ℂ) ((𝓕 w : L2Space E) ξ) * (𝓕 f) ξ := fun f => inner_toL2_fourier w f
  have hright : ∀ f : 𝓢(E, ℂ), inner ℂ y (toL2 (-(Δ f)))
      = ∫ ξ, (starRingEnd ℂ) ((multiplier ξ : ℂ) * (𝓕 y : L2Space E) ξ) * (𝓕 f) ξ := by
    intro f
    rw [inner_toL2_fourier y (-(Δ f))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    dsimp only
    rw [fourier_neg_laplacian_apply, map_mul, Complex.conj_ofReal]
    ring
  constructor
  · intro h
    refine ae_eq_of_integral_contDiff_smul_eq
      (locallyIntegrable_multiplier_mul (locallyIntegrable_L2 (𝓕 y))) (locallyIntegrable_L2 (𝓕 w))
      ?_
    intro g hg hgsupp
    set G : 𝓢(E, ℂ) := (hgsupp.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hg) with hG
    have hGval : ∀ ξ, G ξ = (g ξ : ℂ) := fun ξ => rfl
    have hf := h (𝓕⁻ G)
    rw [hleft, hright] at hf
    rw [FourierTransform.fourier_fourierInv_eq G] at hf
    have hf' := congrArg (starRingEnd ℂ) hf
    rw [← integral_conj, ← integral_conj] at hf'
    simp only [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply] at hf'
    calc ∫ ξ, g ξ • ((multiplier ξ : ℂ) * (𝓕 y : L2Space E) ξ)
        = ∫ ξ, ((multiplier ξ : ℂ) * (𝓕 y : L2Space E) ξ) * (starRingEnd ℂ) (G ξ) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
          dsimp only
          rw [hGval]
          simp [Complex.conj_ofReal, Complex.real_smul]
          ring
      _ = ∫ ξ, ((𝓕 w : L2Space E) ξ) * (starRingEnd ℂ) (G ξ) := hf'.symm
      _ = ∫ ξ, g ξ • ((𝓕 w : L2Space E) ξ) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
          dsimp only
          rw [hGval]
          simp [Complex.conj_ofReal, Complex.real_smul]
          ring
  · intro h f
    rw [hleft, hright]
    refine integral_congr_ae ?_
    filter_upwards [h] with ξ hξ
    rw [hξ]

