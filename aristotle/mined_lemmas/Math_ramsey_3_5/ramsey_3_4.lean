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

lemma ramsey_3_4 (G : SimpleGraph V) (S : Finset V) (hS : 9 ≤ #S) :
    (∃ s ⊆ S, G.IsNClique 3 s) ∨ (∃ t ⊆ S, Gᶜ.IsNClique 4 t) := by
  classical
  obtain ⟨S', hS'sub, hS'card⟩ := Finset.exists_subset_card_eq hS
  suffices h : (∃ s ⊆ S', G.IsNClique 3 s) ∨ (∃ t ⊆ S', Gᶜ.IsNClique 4 t) by
    rcases h with ⟨s, hs, h⟩ | ⟨t, ht, h⟩
    · exact Or.inl ⟨s, hs.trans hS'sub, h⟩
    · exact Or.inr ⟨t, ht.trans hS'sub, h⟩
  clear hS hS'sub
  by_contra hcon
  push_neg at hcon
  obtain ⟨h3, h4⟩ := hcon
  -- every vertex has exactly three neighbours inside `S'`
  have key : ∀ v ∈ S', #{w ∈ S' | G.Adj v w} = 3 := by
    intro v hv
    set A := {w ∈ S'.erase v | G.Adj v w} with hAdef
    set B := {w ∈ S'.erase v | ¬ G.Adj v w} with hBdef
    have hcard : #A + #B = 8 := by
      rw [hAdef, hBdef, Finset.card_filter_add_card_filter_not,
        Finset.card_erase_of_mem hv, hS'card]
    have hAS : A ⊆ S' := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
    have hBS : B ⊆ S' := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
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
    -- at most three neighbours
    have hAle : #A ≤ 3 := by
      by_contra hA
      push_neg at hA
      obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hA
      refine h4 t (hts.trans hAS) ?_
      have := compl_isNClique_of_pairwise_not_adj G t
        (fun a ha b hb hab => hApair a (hts ha) b (hts hb) hab)
      rwa [htc] at this
    -- at most five non-neighbours
    have hBle : #B ≤ 5 := by
      by_contra hB
      push_neg at hB
      rcases ramsey_3_3 G B (by omega) with ⟨s, hs, hsc⟩ | ⟨t, ht, htc⟩
      · exact h3 s (hs.trans hBS) hsc
      · refine h4 (insert v t) ?_ ?_
        · intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · exact hv
          · exact hBS (ht hx)
        · refine compl_isNClique_insert G ?_ ?_ htc
          · intro hvt
            exact (Finset.ne_of_mem_erase (Finset.mem_filter.1 (ht hvt)).1) rfl
          · intro w hw
            exact (Finset.mem_filter.1 (ht hw)).2
    have hAeq : #A = 3 := by omega
    have : {w ∈ S' | G.Adj v w} = A := by
      rw [hAdef]
      ext w
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hw, ha⟩
        exact ⟨⟨fun h => G.irrefl (h ▸ ha), hw⟩, ha⟩
      · rintro ⟨⟨_, hw⟩, ha⟩
        exact ⟨hw, ha⟩
    rw [this, hAeq]
  have hsum : ∑ v ∈ S', #{w ∈ S' | G.Adj v w} = 27 := by
    rw [Finset.sum_congr rfl key, Finset.sum_const, hS'card]
    simp
  have := even_sum_card_filter_adj G S'
  rw [hsum] at this
  exact (by decide : ¬ Even 27) this

