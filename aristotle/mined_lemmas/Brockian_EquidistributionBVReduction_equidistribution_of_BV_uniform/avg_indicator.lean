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

/-
# Equidistribution Of BV Uniform
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Filter Set MeasureTheory
open scoped Topology BigOperators Classical

namespace Brockian.EquidistributionBVReduction

/-- The Cesàro average of `f` along the fractional parts of the sequence `u`. -/

lemma avg_indicator (u : ℕ → ℝ) (a b : ℝ) (N : ℕ) :
    avg u (Set.indicator (Set.Ico a b) (fun _ => (1 : ℝ))) N =
      (((Finset.range N).filter (fun n => Int.fract (u n) ∈ Set.Ico a b)).card : ℝ) / N := by
  unfold avg
  congr 1
  rw [← Finset.sum_boole]
  exact Finset.sum_congr rfl fun n _ => by simp [Set.indicator_apply]

