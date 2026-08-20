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


theorem norm_freeSymbol_mul_freeResolventSymbol_le_one (ξ : V) :
    ‖(freeSymbol ξ : ℂ) * freeResolventSymbol ξ‖ ≤ 1 := by
  have h := one_add_freeSymbol_pos (V := V) ξ
  have h0 := freeSymbol_nonneg (V := V) ξ
  rw [freeResolventSymbol, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  rw [mul_inv_le_iff₀ h, one_mul]
  linarith

end

end Brockian

import Mathlib

/-!
# Multiplication operators on `L²`

For a real-valued continuous function `m` on a finite-dimensional real inner product space `V`
we define the (maximal) multiplication operator `mulOp m` on `L²(V; ℂ)` as an unbounded operator
(a `LinearPMap`), with domain all `u ∈ L²` such that `m * u ∈ L²`.

The main result is `Brockian.mulOp_isSelfAdjoint`: such a multiplication operator is
self-adjoint.
-/

namespace Brockian

open MeasureTheory Filter
open scoped ENNReal ComplexInnerProductSpace Topology

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The complex `L²` space of a finite-dimensional real inner product space, with respect to
the Lebesgue (volume) measure. -/
abbrev L2 (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] := Lp (α := V) ℂ 2 (volume : Measure V)

/-- A pointwise a.e. bound `‖b x‖ ≤ C` on a multiplier gives the corresponding bound on
`L²`-norms. -/
