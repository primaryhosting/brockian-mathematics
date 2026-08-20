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

import Brockian.EquidistributionBVReduction

/-!
# An equidistributed sequence

This file exhibits a concrete sequence in `[0,1)` satisfying
`Brockian.EquidistributionBVReduction.Equidistributed`, showing that the equidistribution
hypothesis of `configCount_density_of_BV` is satisfiable (so the theorem is not vacuous).

The sequence is the "triangular block" sequence: the `k`-th block lists the `k+1` points
`0/(k+1), 1/(k+1), …, k/(k+1)`.
-/

open Filter Set
open scoped Topology

namespace Brockian.EquidistributionBVReduction

/-- Start index of block `k`; block `k` consists of the `k+1` indices
`blockStart k, …, blockStart k + k`. -/

lemma configCount_mono_bounds (x : ℕ → ℝ) (s : Set ℝ) {b N : ℕ} (hbN : b ≤ N) :
    configCount x s b ≤ configCount x s N ∧
      configCount x s N ≤ configCount x s b + (N - b) := by
  have hN : N = b + (N - b) := by omega
  rw [configCount_eq_sum, configCount_eq_sum, hN, Finset.sum_range_add]
  constructor
  · omega
  · have : ∑ i ∈ Finset.range (N - b), (if x (b + i) ∈ s then 1 else 0) ≤ N - b := by
      calc ∑ i ∈ Finset.range (N - b), (if x (b + i) ∈ s then 1 else 0)
          ≤ ∑ _i ∈ Finset.range (N - b), 1 := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            split <;> omega
        _ = N - b := by simp
    omega

