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

lemma configCount_split (x : ℕ → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (N : ℕ) :
    configCount x (Set.Ico 0 b) N
      = configCount x (Set.Ico 0 a) N + configCount x (Set.Ico a b) N := by
  classical
  unfold configCount
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext n
    simp only [Finset.mem_union, Finset.mem_filter, Set.mem_Ico]
    constructor
    · rintro ⟨hn, h0, hb⟩
      rcases lt_or_ge (x n) a with h | h
      · exact Or.inl ⟨hn, h0, h⟩
      · exact Or.inr ⟨hn, h, hb⟩
    · rintro (⟨hn, h0, h⟩ | ⟨hn, h, hb⟩)
      · exact ⟨hn, h0, lt_of_lt_of_le h hab⟩
      · exact ⟨hn, le_trans ha h, hb⟩
  · rw [Finset.disjoint_left]
    intro n hn hn'
    simp only [Finset.mem_filter, Set.mem_Ico] at hn hn'
    linarith [hn.2.2, hn'.2.1]

/-- Densities of half-open subintervals of `[0,1]` are their lengths. -/
