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


theorem freeLaplacian_essentiallySelfAdjoint_via_plancherel :
    IsSelfAdjoint (negLaplacianCore : L2 V →ₗ.[ℂ] L2 V).closure ∧
      ∃! A : L2 V →ₗ.[ℂ] L2 V,
        IsSelfAdjoint A ∧ (negLaplacianCore : L2 V →ₗ.[ℂ] L2 V) ≤ A := by
  refine ⟨by rw [closure_negLaplacianCore]; exact freeLaplacian_isSelfAdjoint,
    ⟨freeLaplacian, ⟨freeLaplacian_isSelfAdjoint, negLaplacianCore_le_freeLaplacian⟩, ?_⟩⟩
  rintro B ⟨hB, hBle⟩
  have h1 : (freeLaplacian : L2 V →ₗ.[ℂ] L2 V) ≤ B := by
    rw [← closure_negLaplacianCore]
    rw [← le_graph_iff, ← negLaplacianCore_isClosable.graph_closure_eq_closure_graph]
    exact Submodule.topologicalClosure_minimal _ (le_graph_of_le hBle) hB.isClosed
  have h2 : B ≤ (freeLaplacian : L2 V →ₗ.[ℂ] L2 V) := by
    have := adjoint_le_adjoint (freeLaplacian_isSelfAdjoint.dense_domain) h1
    rwa [LinearPMap.isSelfAdjoint_def.mp hB, LinearPMap.isSelfAdjoint_def.mp
      freeLaplacian_isSelfAdjoint] at this
  exact le_antisymm h2 h1

end

end Brockian

