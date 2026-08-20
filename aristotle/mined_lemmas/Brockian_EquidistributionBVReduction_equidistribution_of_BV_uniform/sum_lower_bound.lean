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

open Filter Finset MeasureTheory
open scoped Topology BigOperators Classical

namespace Brockian
namespace EquidistributionBVReduction

/-- The number of indices `n < N` for which the fractional part of `x n` lies in `[a, b)`. -/

lemma sum_lower_bound (hg : Monotone g) (x : ℕ → ℝ) {K : ℕ} (hK : 0 < K) (N : ℕ) :
    ∑ i ∈ Finset.range K,
        (countIn x ((i : ℝ) / K) (((i : ℝ) + 1) / K) N : ℝ) * g ((i : ℝ) / K) ≤
      ∑ n ∈ Finset.range N, g (Int.fract (x n)) := by
  rw [sum_eq_sum_fibers x g hK N]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have h := Finset.card_nsmul_le_sum
    ((Finset.range N).filter
      (fun n => Int.fract (x n) ∈ Set.Ico ((i : ℝ) / K) (((i : ℝ) + 1) / K)))
    (fun n => g (Int.fract (x n))) (g ((i : ℝ) / K)) ?_
  · simpa [countIn, nsmul_eq_mul, mul_comm] using h
  · intro n hn
    have := (Finset.mem_filter.1 hn).2
    exact hg this.1

/-- Upper step-function bound for the partial sums. -/
