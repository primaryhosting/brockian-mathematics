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


def mulDomain : Submodule ℂ (L2 V) where
  carrier := {u : L2 V | MemLp (fun x => (m x : ℂ) * (u : V → ℂ) x) 2 (volume : Measure V)}
  add_mem' := by
    intro u v hu hv
    refine (MemLp.add hu hv).ae_eq ?_
    filter_upwards [Lp.coeFn_add u v] with x hx
    simp only [Pi.add_apply] at hx ⊢
    rw [hx]; ring
  zero_mem' := by
    refine (MemLp.zero (p := 2) (μ := (volume : Measure V)) (ε := ℂ)).ae_eq ?_
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure V)] with x hx
    simp
  smul_mem' := by
    intro c u hu
    refine (MemLp.const_smul hu c).ae_eq ?_
    filter_upwards [Lp.coeFn_smul c u] with x hx
    simp only [Pi.smul_apply, smul_eq_mul] at hx ⊢
    rw [hx]; ring

