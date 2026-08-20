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


theorem schwartzToL2_injective : Function.Injective (schwartzToL2 : 𝓢(V, ℂ) → L2 V) := by
  intro f g h
  have h1 : (f : V → ℂ) =ᵐ[volume] (g : V → ℂ) := by
    have hf := SchwartzMap.coeFn_toLp (μ := (volume : Measure V)) (p := 2) f
    have hg := SchwartzMap.coeFn_toLp (μ := (volume : Measure V)) (p := 2) g
    rw [show (f.toLp 2 (volume : Measure V)) = g.toLp 2 (volume : Measure V) from h] at hf
    exact hf.symm.trans hg
  exact SchwartzMap.ext
    (congrFun ((Continuous.ae_eq_iff_eq (volume : Measure V) f.continuous g.continuous).mp h1))

/-- `-Δ` acting on Schwartz functions. -/
