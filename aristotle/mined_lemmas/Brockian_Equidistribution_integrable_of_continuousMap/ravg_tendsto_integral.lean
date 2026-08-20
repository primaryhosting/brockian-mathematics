import Brockian.Equidistribution

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
# Weyl equidistribution

This file develops, from scratch, Weyl's criterion for equidistribution modulo one and applies
it to the sequence `n ↦ n * α` for irrational `α`.

The main statement is `Brockian.Equidistribution.equidistribution_of_asymptotic_exists`, which
is *conditional* on the asymptotic vanishing of the Weyl exponential sums, and its unconditional
consequence `Brockian.Equidistribution.equidistributedMod1_natMul_irrational`.
-/

namespace Brockian.Equidistribution

open MeasureTheory Filter Finset Complex Topology Metric

open scoped Real

noncomputable section

/-- The number of indices `n < N` for which the fractional part of `x n` lies in `[a, b)`. -/

theorem ravg_tendsto_integral (x : ℕ → ℝ) (hx : WeylCondition x) (f : C(AddCircle (1 : ℝ), ℝ)) :
    Tendsto (ravg x f) atTop (𝓝 (∫ z, f z)) := by
  set F : C(AddCircle (1 : ℝ), ℂ) := ⟨fun z => (f z : ℂ), by fun_prop⟩ with hF
  have hc := cavg_tendsto_integral x hx F
  have hint : (∫ z, F z) = ((∫ z, f z : ℝ) : ℂ) := by
    simp only [hF, ContinuousMap.coe_mk]
    exact integral_ofReal
  have hcavg : ∀ N, cavg x F N = ((ravg x f N : ℝ) : ℂ) := by
    intro N
    simp [cavg, ravg, hF]
  rw [hint] at hc
  exact Filter.tendsto_ofReal_iff.mp (hc.congr hcavg)

/-! ### Weyl's criterion, step 3: from continuous functions to intervals -/

/-- A continuous trapezoidal bump on the circle: it equals `1` on the closed arc of radius
`s - ep` around `c`, and vanishes outside the open arc of radius `s`. -/
