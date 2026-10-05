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
