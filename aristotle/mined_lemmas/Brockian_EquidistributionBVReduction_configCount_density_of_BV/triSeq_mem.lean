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

lemma triSeq_mem (n : ℕ) : triSeq n ∈ Set.Ico (0:ℝ) 1 := by
  have h1 := blockStart_blockIdx_le n
  have h2 := lt_blockStart_blockIdx_succ n
  rw [blockStart_succ] at h2
  have hnum : n - blockStart (blockIdx n) < blockIdx n + 1 := by omega
  have hpos : (0:ℝ) < (blockIdx n : ℝ) + 1 := by positivity
  refine ⟨by unfold triSeq; positivity, ?_⟩
  unfold triSeq
  rw [div_lt_one hpos]
  exact_mod_cast hnum

