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

lemma avg_stepFn (u : ℕ → ℝ) (m : ℕ) (c : ℕ → ℝ) (N : ℕ) :
    avg u (stepFn m c) N =
      ∑ i ∈ Finset.range m, c i *
        avg u (Set.indicator (Set.Ico ((i : ℝ) / m) (((i : ℝ) + 1) / m)) (fun _ => (1 : ℝ))) N := by
  simp only [avg, stepFn, Finset.sum_div, mul_div_assoc]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm

