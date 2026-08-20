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

import Mathlib

/-!
# The Fourier transform of the Laplacian on Schwartz space

We record the classical formula `𝓕 (Δ f) ξ = -(4π²‖ξ‖²) 𝓕 f ξ` for Schwartz functions,
introduce the Fourier symbol `freeSymbol ξ = 4π²‖ξ‖²` of the free Laplacian `-Δ`, and show that
the "resolvent multiplier" `ξ ↦ (1 + freeSymbol ξ)⁻¹` has temperate growth (so that multiplying
a Schwartz function by it produces again a Schwartz function).
-/

namespace Brockian

open MeasureTheory SchwartzMap Real LineDeriv
open scoped FourierTransform SchwartzMap ComplexInnerProductSpace

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]


theorem negLaplacianCore_apply (f : 𝓢(V, ℂ)) :
    negLaplacianCore (⟨schwartzToL2 f, mem_negLaplacianCore_domain f⟩ :
      (negLaplacianCore : L2 V →ₗ.[ℂ] L2 V).domain)
      = schwartzToL2 (negLaplacianSchwartz f) := by
  have h : (LinearEquiv.ofInjective (schwartzToL2 : 𝓢(V, ℂ) →ₗ[ℂ] L2 V)
      schwartzToL2_injective).symm ⟨schwartzToL2 f, mem_negLaplacianCore_domain f⟩ = f := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  show (schwartzToL2 ∘ₗ negLaplacianSchwartz) ((LinearEquiv.ofInjective
    (schwartzToL2 : 𝓢(V, ℂ) →ₗ[ℂ] L2 V) schwartzToL2_injective).symm
      ⟨schwartzToL2 f, mem_negLaplacianCore_domain f⟩) = _
  rw [h]
  rfl

