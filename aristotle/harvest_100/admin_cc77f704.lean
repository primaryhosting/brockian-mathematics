/-
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian

/-- The *local constellation count* of a set `S ⊆ ℕ` with respect to a pattern
`h : Fin k → ℕ` in the window `[0, N)`: the number of `n < N` such that the whole
translated constellation `n + h 0, …, n + h (k-1)` lies inside `S`. -/
noncomputable def localConstellationCount {k : ℕ} (S : Set ℕ) (h : Fin k → ℕ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => ∀ i : Fin k, n + h i ∈ S)).card

/-- The number of `n < N` for which the single shift `n + a` fails to lie in `S`. -/
noncomputable def localMissCount (S : Set ℕ) (a N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => n + a ∉ S)).card

/-- Unfolding of the `k = 3` local constellation count as an explicit triple condition. -/
theorem localConstellationCount_three (S : Set ℕ) (a b c N : ℕ) :
    localConstellationCount S ![a, b, c] N
      = ((Finset.range N).filter (fun n => n + a ∈ S ∧ n + b ∈ S ∧ n + c ∈ S)).card := by
  classical
  unfold localConstellationCount
  congr 1
  refine Finset.filter_congr ?_
  intro n _
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i <;> simpa using ‹_›

/-- Unfolding of the `k = 2` local constellation count as an explicit pair condition. -/
theorem localConstellationCount_two (S : Set ℕ) (a b N : ℕ) :
    localConstellationCount S ![a, b] N
      = ((Finset.range N).filter (fun n => n + a ∈ S ∧ n + b ∈ S)).card := by
  classical
  unfold localConstellationCount
  congr 1
  refine Finset.filter_congr ?_
  intro n _
  constructor
  · intro h
    exact ⟨h 0, h 1⟩
  · rintro ⟨h0, h1⟩ i
    fin_cases i <;> simpa using ‹_›

/-- Dropping the third point of a `3`-point constellation can only increase the count. -/
theorem localConstellationCount_three_le_two (S : Set ℕ) (a b c N : ℕ) :
    localConstellationCount S ![a, b, c] N ≤ localConstellationCount S ![a, b] N := by
  classical
  rw [localConstellationCount_three, localConstellationCount_two]
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, hn.2.1, hn.2.2.1⟩

/-- Union bound: the `3`-point constellation count misses at most the sum of the
three individual miss counts. -/
theorem localConstellationCount_three_union_bound (S : Set ℕ) (a b c N : ℕ) :
    N ≤ localConstellationCount S ![a, b, c] N
        + (localMissCount S a N + localMissCount S b N + localMissCount S c N) := by
  classical
  rw [localConstellationCount_three]
  set A := (Finset.range N).filter (fun n => n + a ∉ S) with hA
  set B := (Finset.range N).filter (fun n => n + b ∉ S) with hB
  set C := (Finset.range N).filter (fun n => n + c ∉ S) with hC
  have hsplit :
      ((Finset.range N).filter (fun n => n + a ∈ S ∧ n + b ∈ S ∧ n + c ∈ S)).card
        + ((Finset.range N).filter (fun n => ¬ (n + a ∈ S ∧ n + b ∈ S ∧ n + c ∈ S))).card
        = (Finset.range N).card :=
    Finset.card_filter_add_card_filter_not (s := Finset.range N)
      (fun n => n + a ∈ S ∧ n + b ∈ S ∧ n + c ∈ S)
  have hsub : (Finset.range N).filter (fun n => ¬ (n + a ∈ S ∧ n + b ∈ S ∧ n + c ∈ S))
      ⊆ A ∪ B ∪ C := by
    intro n hn
    simp only [Finset.mem_filter, hA, hB, hC, Finset.mem_union, not_and_or] at hn ⊢
    rcases hn with ⟨hmem, h⟩
    rcases h with h | h | h
    · exact Or.inl (Or.inl ⟨hmem, h⟩)
    · exact Or.inl (Or.inr ⟨hmem, h⟩)
    · exact Or.inr ⟨hmem, h⟩
  have hcard := Finset.card_le_card hsub
  have hcu : (A ∪ B ∪ C).card ≤ A.card + B.card + C.card :=
    (Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  have hrange : (Finset.range N).card = N := Finset.card_range N
  simp only [localMissCount, ← hA, ← hB, ← hC]
  omega

/-- The `3`-point local constellation count is symmetric in its three shifts. -/
theorem localConstellationCount_three_symm (S : Set ℕ) (a b c N : ℕ) :
    localConstellationCount S ![a, b, c] N = localConstellationCount S ![b, a, c] N ∧
    localConstellationCount S ![a, b, c] N = localConstellationCount S ![a, c, b] N := by
  classical
  rw [localConstellationCount_three, localConstellationCount_three,
    localConstellationCount_three]
  constructor
  · congr 1
    refine Finset.filter_congr ?_
    intro n _
    tauto
  · congr 1
    refine Finset.filter_congr ?_
    intro n _
    tauto

/--
**Constellation local count, `k = 3`.**

Extension of the local constellation count to `3`-tuples: for every set `S ⊆ ℕ`,
all shifts `a, b, c` and every window length `N`,

* the count is the number of `n < N` with `n + a, n + b, n + c ∈ S`;
* it is symmetric under permuting the three shifts;
* it is bounded above by the corresponding `2`-point count;
* it satisfies the union (Bonferroni) lower bound
  `N - (miss a + miss b + miss c) ≤ count`.
-/
theorem ConstellationLocalCountK3 (S : Set ℕ) (a b c N : ℕ) :
    localConstellationCount S ![a, b, c] N
        = ((Finset.range N).filter (fun n => n + a ∈ S ∧ n + b ∈ S ∧ n + c ∈ S)).card ∧
      localConstellationCount S ![a, b, c] N = localConstellationCount S ![b, a, c] N ∧
      localConstellationCount S ![a, b, c] N = localConstellationCount S ![a, c, b] N ∧
      localConstellationCount S ![a, b, c] N ≤ localConstellationCount S ![a, b] N ∧
      N ≤ localConstellationCount S ![a, b, c] N
        + (localMissCount S a N + localMissCount S b N + localMissCount S c N) :=
  ⟨localConstellationCount_three S a b c N,
   (localConstellationCount_three_symm S a b c N).1,
   (localConstellationCount_three_symm S a b c N).2,
   localConstellationCount_three_le_two S a b c N,
   localConstellationCount_three_union_bound S a b c N⟩

/-- Sanity check: over the full set the `3`-point local count is the whole window. -/
theorem localConstellationCount_three_univ (a b c N : ℕ) :
    localConstellationCount (Set.univ : Set ℕ) ![a, b, c] N = N := by
  rw [localConstellationCount_three]
  simp

/-- Sanity check: over the empty set the `3`-point local count vanishes. -/
theorem localConstellationCount_three_empty (a b c N : ℕ) :
    localConstellationCount (∅ : Set ℕ) ![a, b, c] N = 0 := by
  rw [localConstellationCount_three]
  simp

end Brockian

