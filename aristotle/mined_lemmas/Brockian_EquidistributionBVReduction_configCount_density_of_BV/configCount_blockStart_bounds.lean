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

lemma configCount_blockStart_bounds (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (K : ℕ) :
    t * blockStart K ≤ (configCount triSeq (Set.Ico 0 t) (blockStart K) : ℝ) ∧
      (configCount triSeq (Set.Ico 0 t) (blockStart K) : ℝ) ≤ t * blockStart K + K := by
  have hsum : ((blockStart K : ℕ) : ℝ) = ∑ k ∈ Finset.range K, ((k:ℝ)+1) := by
    rw [blockStart_eq_sum]
    push_cast
    ring_nf
  rw [configCount_blockStart t ht1 K]
  push_cast
  constructor
  · rw [hsum, Finset.mul_sum]
    exact Finset.sum_le_sum (fun k _ => Nat.le_ceil _)
  · have hb : ∀ k ∈ Finset.range K,
        ((⌈t * ((k:ℝ)+1)⌉₊ : ℝ)) ≤ t * ((k:ℝ)+1) + 1 := by
      intro k _
      have h0 : (0:ℝ) ≤ t * ((k:ℝ)+1) := by positivity
      exact le_of_lt (Nat.ceil_lt_add_one h0)
    calc (∑ k ∈ Finset.range K, (⌈t * ((k:ℝ)+1)⌉₊ : ℝ))
        ≤ ∑ k ∈ Finset.range K, (t * ((k:ℝ)+1) + 1) := Finset.sum_le_sum hb
      _ = t * blockStart K + K := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hsum]
          simp

open Classical in
/-- Monotonicity and a crude upper bound for counts along the sequence. -/
