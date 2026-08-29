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
# Equidistribution Of BV Uniform
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Filter Set MeasureTheory Topology

namespace Brockian.EquidistributionBVReduction

/-- The indicator function of the half-open interval `[a, b)`, as a real-valued function. -/

lemma sum_indicatorIco_eq_card (x : ℕ → ℝ) (a b : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, indicatorIco a b (x n))
      = (((Finset.range N).filter (fun n => x n ∈ Set.Ico a b)).card : ℝ) := by
  classical
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun n _ => ?_
  simp [indicatorIco, Set.indicator_apply]

/-- **Reduction of equidistribution to bounded-variation test functions.**

If the Cesàro averages of `f (x n)` converge to `∫₀¹ f` for every function `f` of bounded
variation on `[0, 1]` which is interval integrable there (the "BV-uniform" hypothesis), then the
sequence `x` is equidistributed: for every subinterval `[a, b) ⊆ [0, 1]`, the proportion of
indices `n < N` with `x n ∈ [a, b)` tends to `b - a`.

The proof applies the hypothesis to the indicator function of `[a, b)`, which is shown here to
be of bounded variation on `[0, 1]` (it is the difference of two monotone half-line indicators)
and interval integrable, with `∫₀¹ 1_{[a,b)} = b - a`. -/
