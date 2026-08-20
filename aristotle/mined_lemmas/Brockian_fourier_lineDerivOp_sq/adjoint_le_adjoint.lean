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


theorem adjoint_le_adjoint {S T : E →ₗ.[𝕜] E} (hS : Dense (S.domain : Set E)) (h : S ≤ T) :
    T.adjoint ≤ S.adjoint := by
  have hT : Dense (T.domain : Set E) := hS.mono h.1
  refine LinearPMap.IsFormalAdjoint.le_adjoint hS ?_
  intro x y
  have hx : (x : E) ∈ T.domain := h.1 x.2
  have hSx : S x = T ⟨(x : E), hx⟩ := h.2 rfl
  rw [hSx]
  exact inner_apply_adjoint T hT ⟨(x : E), hx⟩ y

end

end Brockian

import Brockian.MultiplicationOperator
import Brockian.PMapConjugation
import Brockian.SchwartzFourierLaplacian
import Brockian.SchwartzCore

/-!
# Essential self-adjointness of the free Laplacian, via Plancherel

Let `V` be a finite-dimensional real inner product space and let `H = L²(V; ℂ)`.

We consider the *free Laplacian* `-Δ`, defined on the core of Schwartz functions
(`negLaplacianCore`), and the operator `freeLaplacian`, which is the conjugate under the
(unitary, by Plancherel) Fourier transform of the maximal multiplication operator by the symbol
`freeSymbol ξ = 4π²‖ξ‖²`.

The main theorem `freeLaplacian_essentiallySelfAdjoint_via_plancherel` states that `-Δ` defined
on Schwartz functions is *essentially self-adjoint*: its closure is self-adjoint, and it admits
exactly one self-adjoint extension.
-/

namespace Brockian

open MeasureTheory SchwartzMap Filter LinearPMap LineDeriv
open scoped FourierTransform SchwartzMap ComplexInnerProductSpace Topology

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The Fourier transform as a unitary of `L²(V; ℂ)` (Plancherel's theorem). -/
abbrev fourierU (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] : L2 V ≃ₗᵢ[ℂ] L2 V := Lp.fourierTransformₗᵢ V ℂ

/-- The free Laplacian `-Δ` with its maximal domain, defined as the conjugate under the Fourier
transform of the multiplication operator by the symbol `4π²‖ξ‖²`. -/
