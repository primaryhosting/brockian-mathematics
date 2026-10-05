import Brockian.EquidistributionBVReduction

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

open Filter Set MeasureTheory
open scoped BigOperators Topology

namespace Brockian
namespace EquidistributionBVReduction

/-- The empirical frequency with which the first `N` terms of the sequence `x`
land in the interval `[a, b)`. -/

lemma sum_stepFun (x : ℕ → ℝ) (k : ℕ) (c : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, stepFun k c (x n)
      = ∑ i ∈ Finset.range k,
          c i * (((Finset.range N).filter
            (fun n => x n ∈ Set.Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k))).card : ℝ) := by
  classical
  simp only [stepFun]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.card_filter]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h : x n ∈ Set.Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)
  · simp [h]
  · simp [h]

