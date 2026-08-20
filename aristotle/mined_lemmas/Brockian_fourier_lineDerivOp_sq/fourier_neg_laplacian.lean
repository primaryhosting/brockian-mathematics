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


theorem fourier_neg_laplacian (f : 𝓢(V, ℂ)) (ξ : V) :
    𝓕 (-(laplacianCLM ℂ V 𝓢(V, ℂ) f)) ξ = (freeSymbol ξ : ℂ) * 𝓕 f ξ := by
  have : 𝓕 (-(laplacianCLM ℂ V 𝓢(V, ℂ) f)) = -𝓕 (laplacianCLM ℂ V 𝓢(V, ℂ) f) := by
    rw [← fourierTransformCLM_apply (𝕜 := ℂ), ← fourierTransformCLM_apply (𝕜 := ℂ), map_neg]
  rw [this]
  simp only [SchwartzMap.neg_apply, fourier_laplacian f ξ, freeSymbol]
  push_cast
  ring

/-- The resolvent multiplier `(1 + freeSymbol)⁻¹`, as a complex-valued function. -/
