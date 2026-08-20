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
# Equidistribution of irrational rotations, and the density of configuration counts

This file proves Weyl's equidistribution theorem for the sequence `n ↦ {n α}` (`α` irrational)
and deduces the unconditional statement `configCount_density_of_BV`: the density of the set of
`n < N` with `{n α} ∈ [a, b)` tends to `b - a`.

The indicator of an interval is the basic example of a function of bounded variation, and the
"BV reduction" is implemented here through the portmanteau theorem: the empirical measures of
the orbit converge weakly to Haar measure (proved via the Fourier/Weyl criterion), hence the
measures of any arc whose boundary is Haar-null converge.
-/

namespace Brockian
namespace EquidistributionBVReduction

open Filter MeasureTheory Set Topology AddCircle
open scoped BigOperators ENNReal NNReal

/-- The point `n • α` of the circle `ℝ / ℤ`. -/

lemma empMeasure_arc {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (alpha : ℝ) (N : ℕ) :
    empMeasure alpha N (arc a b) = (N : ℝ≥0∞)⁻¹ * (configCount alpha a b N : ℝ≥0∞) := by
  rw [empMeasure, Measure.smul_apply, Measure.finset_sum_apply, smul_eq_mul]
  congr 1
  rw [configCount, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.dirac_apply' _ (measurableSet_arc a b)]
  simp only [orbitPoint]
  by_cases h : Int.fract ((i:ℝ) * alpha) ∈ Set.Ico a b
  · rw [if_pos h, Set.indicator_of_mem ((mem_arc_iff ha hb _).mpr h)]
    simp
  · rw [if_neg h, Set.indicator_of_notMem (fun hc => h ((mem_arc_iff ha hb _).mp hc))]

/-! ### Main theorem -/

/-- **Weyl equidistribution / density of configuration counts.**
For irrational `α` and `0 ≤ a ≤ b ≤ 1`, the proportion of `n < N` with `{n α} ∈ [a, b)`
converges to `b - a`.

The statement is unconditional: no equidistribution assumption is taken as a hypothesis.
The equidistribution input is supplied by `tendsto_avg_continuous` (Weyl's criterion together
with density of trigonometric polynomials) and `tendsto_empProb` (weak convergence of the
empirical measures), and the passage from continuous test functions to the indicator of an
interval — the basic bounded-variation test function — is the portmanteau theorem applied to
the arc `arc a b`, whose boundary is Haar-null. -/
