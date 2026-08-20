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


theorem dense_negLaplacianCore_domain :
    Dense (((negLaplacianCore : L2 V →ₗ.[ℂ] L2 V).domain : Submodule ℂ (L2 V)) : Set (L2 V)) := by
  have h := SchwartzMap.denseRange_toLpCLM (E := V) (F := ℂ) (p := 2) ENNReal.ofNat_ne_top
    (μ := (volume : Measure V))
  have : ((LinearMap.range (schwartzToL2 : 𝓢(V, ℂ) →ₗ[ℂ] L2 V) : Submodule ℂ (L2 V)) : Set (L2 V))
      = Set.range (fun f : 𝓢(V, ℂ) => f.toLp 2 (volume : Measure V)) := by
    ext x
    simp [LinearMap.mem_range, schwartzToL2]
  show Dense (((LinearMap.range (schwartzToL2 : 𝓢(V, ℂ) →ₗ[ℂ] L2 V)) : Submodule ℂ (L2 V)) :
    Set (L2 V))
  rw [this]
  exact h

end

end Brockian

import Mathlib

/-!
# Conjugation of unbounded operators by a unitary

If `U` is a unitary (a surjective linear isometry) of a Hilbert space `E` and `T` is an unbounded
operator on `E`, then `conjPMap U T = U⁻¹ ∘ T ∘ U` is again an unbounded operator, and taking
adjoints commutes with this conjugation.  In particular the conjugate of a self-adjoint operator
is self-adjoint.
-/

namespace Brockian

open LinearPMap

noncomputable section

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The conjugate `U⁻¹ ∘ T ∘ U` of an unbounded operator `T` by a unitary `U`. -/
