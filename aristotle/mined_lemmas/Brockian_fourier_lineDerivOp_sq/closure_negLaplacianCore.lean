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


theorem closure_negLaplacianCore :
    (negLaplacianCore : L2 V →ₗ.[ℂ] L2 V).closure = freeLaplacian := by
  refine le_antisymm ?_ ?_
  · rw [← le_graph_iff, ← negLaplacianCore_isClosable.graph_closure_eq_closure_graph]
    exact Submodule.topologicalClosure_minimal _ (le_graph_of_le negLaplacianCore_le_freeLaplacian)
      freeLaplacian_isSelfAdjoint.isClosed
  · refine le_of_le_graph ?_
    rw [← negLaplacianCore_isClosable.graph_closure_eq_closure_graph]
    rintro ⟨x, y⟩ hxy
    rw [LinearPMap.mem_graph_iff] at hxy
    obtain ⟨u, hu⟩ := hxy
    obtain ⟨f, hf1, hf2⟩ := exists_schwartz_graph_approx u
    have hx : (u : L2 V) = x := hu.1
    have hy : freeLaplacian u = y := hu.2
    rw [hx] at hf1
    rw [hy] at hf2
    refine mem_closure_of_tendsto (hf1.prodMk_nhds hf2) (Filter.Eventually.of_forall ?_)
    intro k
    have := LinearPMap.mem_graph (negLaplacianCore : L2 V →ₗ.[ℂ] L2 V)
      ⟨schwartzToL2 (f k), mem_negLaplacianCore_domain (f k)⟩
    rwa [negLaplacianCore_apply] at this

/-- **Essential self-adjointness of the free Laplacian.**

The Laplacian `-Δ`, defined on the core of Schwartz functions inside `L²(V; ℂ)`, is essentially
self-adjoint: its closure is a self-adjoint operator, and it has exactly one self-adjoint
extension (namely the operator `freeLaplacian` obtained from the Fourier multiplier `4π²‖ξ‖²`). -/
