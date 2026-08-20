import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

private lemma pf_map_tail {L : List (List Bool)} (h : PFList L)
    (hne : ∀ x ∈ L, x ≠ []) (hhead : ∀ x ∈ L, ∀ y ∈ L, x.headI = y.headI) :
    PFList (L.map List.tail) := by
  rw [PFList, List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_ h
  intro a b ha hb hab
  have hane := hne a ha
  have hbne := hne b hb
  have hh := hhead a ha b hb
  constructor
  · intro hpre
    refine hab.1 ?_
    obtain ⟨a1, a2, rfl⟩ : ∃ c cs, a = c :: cs := by
      cases a with
      | nil => exact absurd rfl hane
      | cons c cs => exact ⟨c, cs, rfl⟩
    obtain ⟨b1, b2, rfl⟩ : ∃ c cs, b = c :: cs := by
      cases b with
      | nil => exact absurd rfl hbne
      | cons c cs => exact ⟨c, cs, rfl⟩
    simp only [List.headI] at hh
    simp only [List.tail] at hpre
    exact List.cons_prefix_cons.mpr ⟨hh, hpre⟩
  · intro hpre
    refine hab.2 ?_
    obtain ⟨a1, a2, rfl⟩ : ∃ c cs, a = c :: cs := by
      cases a with
      | nil => exact absurd rfl hane
      | cons c cs => exact ⟨c, cs, rfl⟩
    obtain ⟨b1, b2, rfl⟩ : ∃ c cs, b = c :: cs := by
      cases b with
      | nil => exact absurd rfl hbne
      | cons c cs => exact ⟨c, cs, rfl⟩
    simp only [List.headI] at hh
    simp only [List.tail] at hpre
    exact List.cons_prefix_cons.mpr ⟨hh.symm, hpre⟩

