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

lemma block_count_eq (t : ℝ) (ht1 : t ≤ 1) (k : ℕ) :
    (∑ i ∈ Finset.range (k+1), if ((i:ℝ)/((k:ℝ)+1)) ∈ Set.Ico (0:ℝ) t then 1 else 0)
      = ⌈t * ((k:ℝ)+1)⌉₊ := by
  have hpos : (0:ℝ) < (k:ℝ) + 1 := by positivity
  have hceil_le : ⌈t * ((k:ℝ)+1)⌉₊ ≤ k + 1 := by
    rw [Nat.ceil_le]
    push_cast
    nlinarith
  have hset : (Finset.range (k+1)).filter (fun i : ℕ => ((i:ℝ)/((k:ℝ)+1)) ∈ Set.Ico (0:ℝ) t)
      = Finset.range ⌈t * ((k:ℝ)+1)⌉₊ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_Ico]
    constructor
    · rintro ⟨hi, h0, hlt⟩
      rw [div_lt_iff₀ hpos] at hlt
      exact Nat.lt_ceil.2 (by linarith)
    · intro hi
      have h1 : (i:ℝ) < t * ((k:ℝ)+1) := Nat.lt_ceil.1 hi
      refine ⟨by omega, by positivity, ?_⟩
      rw [div_lt_iff₀ hpos]
      linarith
  rw [← Finset.card_filter, hset, Finset.card_range]

open Classical in
/-- The count over a full prefix of blocks. -/
