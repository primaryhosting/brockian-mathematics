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

namespace Brockian.Weyl.FreeLaplacian2

open MeasureTheory SchwartzMap Real LineDeriv
open scoped FourierTransform InnerProductSpace Laplacian

noncomputable section

/-- A densely defined operator `A` on a Hilbert space is *essentially self-adjoint* if its
adjoint is self-adjoint (equivalently, if the closure `A** = A*` of `A` is self-adjoint). -/

lemma fourier_adjoint_apply (g : (freeLaplacian V).adjoint.domain) :
    ((𝓕 ((freeLaplacian V).adjoint g) : L2Space V) : V → ℂ)
      =ᵐ[volume] fun ξ => (multiplier ξ : ℂ) * ((𝓕 (g : L2Space V) : L2Space V) : V → ℂ) ξ := by
  refine ae_eq_multiplier_mul V _ _ ?_
  intro φ
  set f : 𝓢(V, ℂ) := 𝓕⁻ φ with hf
  have hfφ : 𝓕 f = φ := FourierTransform.fourier_fourierInv_eq φ
  have hform := LinearPMap.adjoint_isFormalAdjoint (dense_domain_freeLaplacian V) g
    ⟨toL2 V f, mem_domain_freeLaplacian V f⟩
  rw [freeLaplacian_apply] at hform
  have hL : inner ℂ (𝓕 ((freeLaplacian V).adjoint g) : L2Space V) (toL2 V φ)
      = inner ℂ ((freeLaplacian V).adjoint g) (toL2 V f) := by
    rw [← hfφ, ← fourier_toL2, MeasureTheory.Lp.inner_fourier_eq]
  have hR : inner ℂ (𝓕 (g : L2Space V) : L2Space V) (toL2 V (mulMultiplier V φ))
      = inner ℂ (g : L2Space V) (toL2 V (-(Δ f))) := by
    rw [← hfφ, mulMultiplier_fourier, ← fourier_toL2, MeasureTheory.Lp.inner_fourier_eq]
  rw [hL, hR]
  exact hform

