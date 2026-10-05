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

lemma freeLaplacian_apply (f : 𝓢(V, ℂ)) :
    (freeLaplacian V) ⟨toL2 V f, mem_domain_freeLaplacian V f⟩ = toL2 V (-(Δ f)) := by
  have h : (LinearEquiv.ofInjective (toL2 V) (toL2_injective V)).symm
      ⟨toL2 V f, mem_domain_freeLaplacian V f⟩ = f := by
    apply (LinearEquiv.symm_apply_eq _).2
    exact Subtype.ext rfl
  show (toL2 V ∘ₗ (-(laplacianCLM ℂ V 𝓢(V, ℂ)).toLinearMap))
      ((LinearEquiv.ofInjective (toL2 V) (toL2_injective V)).symm
        ⟨toL2 V f, mem_domain_freeLaplacian V f⟩) = _
  rw [h]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.neg_apply,
    ContinuousLinearMap.coe_coe, SchwartzMap.laplacianCLM_eq, toL2_apply, map_neg]

