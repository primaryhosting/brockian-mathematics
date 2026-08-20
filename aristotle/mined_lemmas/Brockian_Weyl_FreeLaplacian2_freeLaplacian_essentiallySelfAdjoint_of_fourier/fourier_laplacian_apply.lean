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

theorem fourier_laplacian_apply (f : 𝓢(E, ℂ)) (ξ : E) :
    𝓕 (Δ f) ξ = -(multiplier ξ : ℂ) * 𝓕 f ξ := by
  classical
  set b := stdOrthonormalBasis ℝ E with hb
  rw [SchwartzMap.laplacian_eq_sum b f, fourier_sum, SchwartzMap.sum_apply]
  have key : ∀ i, 𝓕 (∂_{b i} (∂_{b i} f)) ξ
      = (-((inner ℝ ξ (b i) : ℝ)) ^ 2 : ℝ) * ((4 * π ^ 2 : ℝ) * 𝓕 f ξ) := by
    intro i
    rw [fourier_lineDeriv_apply, fourier_lineDeriv_apply]
    push_cast
    ring_nf
    simp [Complex.I_sq]
  simp_rw [key]
  rw [← Finset.sum_mul]
  have hsum : ∑ i, ((-((inner ℝ ξ (b i) : ℝ)) ^ 2 : ℝ) : ℂ) = ((-‖ξ‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sum]
    congr 1
    rw [← b.sum_sq_inner_left ξ, ← Finset.sum_neg_distrib]
  rw [hsum]
  simp only [multiplier]
  push_cast
  ring

