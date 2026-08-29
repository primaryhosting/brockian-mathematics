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
# Friendship Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.friendship_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset Matrix SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A graph satisfies the *friendship condition* when any two distinct vertices have
exactly one common neighbour ("every two people have exactly one common friend"). -/

lemma three_le_degree (hG : Friendship G) (hnp : ∀ u : V, ∃ w : V, w ≠ u ∧ ¬ G.Adj u w)
    {d : ℕ} (hd : ∀ v : V, G.degree v = d) (v : V) : 3 ≤ d := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨w, hwv, hvw⟩ := hnp v
  obtain ⟨u, ⟨hvu, hwu⟩, -⟩ := hG (Ne.symm hwv)
  interval_cases d
  · -- degree `0` is impossible: `u` is a neighbour of `v`
    have hmem : u ∈ G.neighborFinset v := by rw [mem_neighborFinset]; exact hvu
    have hpos := Finset.card_pos.mpr ⟨u, hmem⟩
    rw [card_neighborFinset_eq_degree, hd] at hpos
    omega
  · -- degree `1` is impossible: `u` is adjacent to both `v` and `w`
    have hsub : ({v, w} : Finset V) ⊆ G.neighborFinset u := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · rw [mem_neighborFinset]; exact hvu.symm
      · rw [mem_neighborFinset]; exact hwu.symm
    have hcard := Finset.card_le_card hsub
    rw [card_neighborFinset_eq_degree, hd,
      Finset.card_insert_of_notMem (by simpa using Ne.symm hwv), Finset.card_singleton] at hcard
    omega
  · -- degree `2` is impossible: then there are only three vertices
    have hcardV := card_eq_of_regular hG hd v
    have hsub : G.neighborFinset v ⊆ (Finset.univ.erase v).erase w := by
      intro x hx
      rw [mem_neighborFinset] at hx
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ x⟩⟩
      · rintro rfl; exact hvw hx
      · rintro rfl; exact G.irrefl hx
    have hc := Finset.card_le_card hsub
    rw [card_neighborFinset_eq_degree, hd, Finset.card_erase_of_mem
      (Finset.mem_erase.mpr ⟨hwv, Finset.mem_univ w⟩), Finset.card_erase_of_mem (Finset.mem_univ v),
      Finset.card_univ] at hc
    omega

/-- The main counting contradiction: a regular friendship graph of degree at least three cannot
exist.  Working modulo a prime `p` dividing `d - 1`, the adjacency matrix `A` satisfies
`A ^ k = J` (the all-ones matrix) for all `k ≥ 2`; comparing `trace (A ^ p) = (trace A) ^ p = 0`
with `trace J = n = 1` gives `1 = 0` in `ZMod p`. -/
