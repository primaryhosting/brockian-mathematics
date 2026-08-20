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


def mulOp : L2 V →ₗ.[ℂ] L2 V where
  domain := mulDomain m
  toFun :=
    { toFun := mulFun m
      map_add' := by
        intro u v
        refine Lp.ext ?_
        filter_upwards [coeFn_mulFun m (u + v), coeFn_mulFun m u, coeFn_mulFun m v,
          Lp.coeFn_add (mulFun m u) (mulFun m v), Lp.coeFn_add (u : L2 V) (v : L2 V)]
          with x h1 h2 h3 h4 h5
        simp only [Pi.add_apply] at *
        rw [h1, h4, h2, h3,
          show ((u + v : mulDomain m) : L2 V) = (u : L2 V) + (v : L2 V) from rfl, h5]
        ring
      map_smul' := by
        intro c u
        refine Lp.ext ?_
        filter_upwards [coeFn_mulFun m (c • u), coeFn_mulFun m u,
          Lp.coeFn_smul c (mulFun m u), Lp.coeFn_smul c (u : L2 V)] with x h1 h2 h3 h4
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply] at *
        rw [h1, h3, h2,
          show ((c • u : mulDomain m) : L2 V) = c • (u : L2 V) from rfl, h4]
        ring }

