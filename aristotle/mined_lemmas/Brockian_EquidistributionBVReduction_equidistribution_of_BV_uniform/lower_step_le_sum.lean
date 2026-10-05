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

open Filter Finset MeasureTheory Set
open scoped Topology

namespace Brockian.EquidistributionBVReduction

/-- The frequency with which the fractional parts of the first `N` terms of the sequence `x`
land in the interval `[a, b)`. -/

lemma lower_step_le_sum (hg : MonotoneOn g (Set.Icc (0 : ℝ) 1)) (x : ℕ → ℝ) {k : ℕ} (hk : 0 < k)
    (N : ℕ) :
    ∑ j ∈ Finset.range k, g ((j : ℝ) / k) *
        (((Finset.range N).filter
          (fun n => Int.fract (x n) ∈ Set.Ico ((j : ℝ) / k) (((j : ℝ) + 1) / k))).card : ℝ) ≤
      ∑ n ∈ Finset.range N, g (Int.fract (x n)) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  rw [← Finset.sum_fiberwise_of_maps_to (index_mem_range x hk N) (fun n => g (Int.fract (x n)))]
  refine Finset.sum_le_sum (fun j hj => ?_)
  rw [fiber_eq_filter_Ico x hk N j]
  have hjk : ((j:ℝ) + 1) / k ≤ 1 := by
    rw [div_le_one hk0]
    have : j + 1 ≤ k := Finset.mem_range.mp hj
    exact_mod_cast this
  have hj1 : (j:ℝ)/k ≤ ((j:ℝ)+1)/k := by gcongr; linarith
  have hj0 : (0:ℝ) ≤ (j:ℝ)/k := by positivity
  calc g ((j:ℝ)/k) * _
      = ∑ _n ∈ (Finset.range N).filter
          (fun n => Int.fract (x n) ∈ Set.Ico ((j : ℝ) / k) (((j : ℝ) + 1) / k)),
          g ((j:ℝ)/k) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ n ∈ (Finset.range N).filter
          (fun n => Int.fract (x n) ∈ Set.Ico ((j : ℝ) / k) (((j : ℝ) + 1) / k)),
          g (Int.fract (x n)) := by
        refine Finset.sum_le_sum (fun n hn => ?_)
        have hmem := (Finset.mem_filter.mp hn).2
        exact hg ⟨hj0, hj1.trans hjk⟩
          ⟨Int.fract_nonneg _, le_of_lt (lt_of_lt_of_le hmem.2 hjk)⟩ hmem.1

/-- The lower Riemann sum of a monotone function is at most its integral. -/
