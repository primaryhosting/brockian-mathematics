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


theorem conjPMap_adjoint (hT : Dense (T.domain : Set E)) :
    (conjPMap U T).adjoint = conjPMap U T.adjoint := by
  have hcd : Dense (((conjPMap U T).domain : Submodule 𝕜 E) : Set E) :=
    dense_conjPMap_domain U T hT
  refine le_antisymm ?_ ?_
  · have hdom : ((conjPMap U T).adjoint).domain ≤ (conjPMap U T.adjoint).domain := by
      intro y hy
      show U y ∈ T.adjoint.domain
      refine LinearPMap.mem_adjoint_domain_of_exists _
        ⟨U ((conjPMap U T).adjoint ⟨y, hy⟩), ?_⟩
      intro x
      have hx : U (U.symm (x : E)) ∈ T.domain := by simp
      have h1 := LinearPMap.adjoint_isFormalAdjoint hcd ⟨y, hy⟩ ⟨U.symm (x : E), hx⟩
      have hxx : (⟨U (U.symm (x : E)), hx⟩ : T.domain) = x := Subtype.ext (by simp)
      have h2 : conjPMap U T ⟨U.symm (x : E), hx⟩ = U.symm (T x) := by
        rw [conjPMap_apply U T ⟨U.symm (x : E), hx⟩ hx, hxx]
      rw [h2] at h1
      calc inner 𝕜 (U ((conjPMap U T).adjoint ⟨y, hy⟩)) (x : E)
          = inner 𝕜 ((conjPMap U T).adjoint ⟨y, hy⟩) (U.symm (x : E)) := by
            rw [← U.inner_map_map ((conjPMap U T).adjoint ⟨y, hy⟩) (U.symm (x : E))]
            simp
        _ = inner 𝕜 y (U.symm (T x)) := h1
        _ = inner 𝕜 (U y) (T x) := by
            rw [← U.inner_map_map y (U.symm (T x))]
            simp
    refine ⟨hdom, ?_⟩
    intro p q hpq
    have hq : U (q : E) ∈ T.adjoint.domain := q.2
    refine LinearPMap.adjoint_apply_eq hcd p ?_
    intro z
    have hz : U (z : E) ∈ T.domain := z.2
    have h1 : conjPMap U T.adjoint q = U.symm (T.adjoint ⟨U (q : E), hq⟩) := rfl
    calc inner 𝕜 (conjPMap U T.adjoint q) (z : E)
        = inner 𝕜 (U (q : E)) (T ⟨U (z : E), hz⟩) := by
          rw [h1, ← U.inner_map_map (U.symm (T.adjoint ⟨U (q : E), hq⟩)) (z : E)]
          simp only [LinearIsometryEquiv.apply_symm_apply]
          exact LinearPMap.adjoint_isFormalAdjoint hT ⟨U (q : E), hq⟩ ⟨U (z : E), hz⟩
      _ = inner 𝕜 (q : E) (conjPMap U T z) := by
          rw [conjPMap_apply U T z hz, ← U.inner_map_map (q : E) (U.symm (T ⟨U (z : E), hz⟩))]
          simp
      _ = inner 𝕜 (p : E) (conjPMap U T z) := by rw [hpq]
  · refine LinearPMap.IsFormalAdjoint.le_adjoint hcd ?_
    intro x y
    have hx : U (x : E) ∈ T.domain := x.2
    have hy : U (y : E) ∈ T.adjoint.domain := y.2
    have h1 : conjPMap U T x = U.symm (T ⟨U (x : E), hx⟩) := rfl
    have h2 : conjPMap U T.adjoint y = U.symm (T.adjoint ⟨U (y : E), hy⟩) := rfl
    rw [h1, h2]
    rw [show inner 𝕜 (U.symm (T ⟨U (x : E), hx⟩)) (y : E)
        = inner 𝕜 (T ⟨U (x : E), hx⟩) (U (y : E)) by
      rw [← U.inner_map_map (U.symm (T ⟨U (x : E), hx⟩)) (y : E)]
      simp]
    rw [show inner 𝕜 (x : E) (U.symm (T.adjoint ⟨U (y : E), hy⟩))
        = inner 𝕜 (U (x : E)) (T.adjoint ⟨U (y : E), hy⟩) by
      rw [← U.inner_map_map (x : E) (U.symm (T.adjoint ⟨U (y : E), hy⟩))]
      simp]
    exact inner_apply_adjoint T hT ⟨U (x : E), hx⟩ ⟨U (y : E), hy⟩

/-- The conjugate of a self-adjoint operator by a unitary is self-adjoint. -/
