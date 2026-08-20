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


theorem hasTemperateGrowth_freeResolventSymbol :
    Function.HasTemperateGrowth (freeResolventSymbol : V → ℂ) := by
  have hscale : Function.HasTemperateGrowth (fun ξ : V => (2 * π : ℝ) • ξ) := by
    have := ((2 * π : ℝ) • ContinuousLinearMap.id ℝ V).hasTemperateGrowth
    simpa using this
  have hb : Function.HasTemperateGrowth (fun y : V => (1 + ‖y‖ ^ 2) ^ (-1 : ℝ)) :=
    Function.hasTemperateGrowth_one_add_norm_sq_rpow V (-1)
  have hcomp : Function.HasTemperateGrowth (fun ξ : V => (1 + ‖(2 * π : ℝ) • ξ‖ ^ 2) ^ (-1 : ℝ)) :=
    hb.comp hscale
  have heq : (fun ξ : V => (1 + ‖(2 * π : ℝ) • ξ‖ ^ 2) ^ (-1 : ℝ))
      = (fun ξ : V => (1 + freeSymbol ξ)⁻¹) := by
    funext ξ
    rw [Real.rpow_neg_one, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
    congr 1
    simp only [freeSymbol, mul_pow]
    ring
  rw [heq] at hcomp
  have h2 := Function.HasTemperateGrowth.comp Function.Complex.hasTemperateGrowth_ofReal hcomp
  have h3 : (Complex.ofReal ∘ fun ξ : V => (1 + freeSymbol ξ)⁻¹) = (freeResolventSymbol : V → ℂ) :=
    rfl
  rwa [h3] at h2

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
