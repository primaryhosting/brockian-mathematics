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

/-
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset SimpleGraph

namespace Ramsey35

variable {V : Type*} [DecidableEq V]

/-! ### Basic clique helpers -/

omit [DecidableEq V] in
/-- A finset all of whose distinct pairs are non-adjacent is a clique in the complement. -/

lemma ramsey_3_3 (G : SimpleGraph V) (S : Finset V) (hS : 6 ≤ #S) :
    (∃ s ⊆ S, G.IsNClique 3 s) ∨ (∃ t ⊆ S, Gᶜ.IsNClique 3 t) := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨h3, h4⟩ := hcon
  obtain ⟨v, hv⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  set A := {w ∈ S.erase v | G.Adj v w} with hAdef
  set B := {w ∈ S.erase v | ¬ G.Adj v w} with hBdef
  have hcard : #A + #B = #S - 1 := by
    rw [hAdef, hBdef, Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem hv]
  have hAS : A ⊆ S := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
  have hBS : B ⊆ S := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
  -- neighbours are pairwise non-adjacent
  have hApair : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ G.Adj a b := by
    intro a ha b hb hab hadj
    rw [hAdef, Finset.mem_filter] at ha hb
    refine h3 {v, a, b} ?_ ?_
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hv
      · exact Finset.mem_of_mem_erase ha.1
      · exact Finset.mem_of_mem_erase hb.1
    · exact SimpleGraph.is3Clique_triple_iff.2 ⟨ha.2, hb.2, hadj⟩
  -- non-neighbours are pairwise adjacent
  have hBpair : ∀ a ∈ B, ∀ b ∈ B, a ≠ b → G.Adj a b := by
    intro a hb' b hb hab
    by_contra hadj
    rw [hBdef, Finset.mem_filter] at hb' hb
    refine h4 {v, a, b} ?_ ?_
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hv
      · exact Finset.mem_of_mem_erase hb'.1
      · exact Finset.mem_of_mem_erase hb.1
    · refine SimpleGraph.is3Clique_triple_iff.2 ⟨?_, ?_, ?_⟩
      · exact (SimpleGraph.compl_adj G _ _).2
          ⟨fun h => (Finset.ne_of_mem_erase hb'.1) h.symm, hb'.2⟩
      · exact (SimpleGraph.compl_adj G _ _).2
          ⟨fun h => (Finset.ne_of_mem_erase hb.1) h.symm, hb.2⟩
      · exact (SimpleGraph.compl_adj G _ _).2 ⟨hab, hadj⟩
  rcases (by omega : 3 ≤ #A ∨ 3 ≤ #B) with hA3 | hB3
  · obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hA3
    refine h4 t (hts.trans hAS) ?_
    have := compl_isNClique_of_pairwise_not_adj G t
      (fun a ha b hb hab => hApair a (hts ha) b (hts hb) hab)
    rwa [htc] at this
  · obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hB3
    refine h3 t (hts.trans hBS) ?_
    have := isNClique_of_pairwise_adj G t
      (fun a ha b hb hab => hBpair a (hts ha) b (hts hb) hab)
    rwa [htc] at this

