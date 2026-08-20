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

lemma configCount_blockStart (t : ℝ) (ht1 : t ≤ 1) (K : ℕ) :
    configCount triSeq (Set.Ico 0 t) (blockStart K)
      = ∑ k ∈ Finset.range K, ⌈t * ((k:ℝ)+1)⌉₊ := by
  rw [configCount_eq_sum, sum_range_blockStart]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← block_count_eq t ht1 k]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [triSeq_block k i (Finset.mem_range.1 hi)]
  congr 1

/-- Two-sided bound for the count over a full prefix of blocks. -/
