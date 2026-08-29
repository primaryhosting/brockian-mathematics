import Mathlib
import RequestProject.Paley

/-!
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

open Finset

/-! ## Monochromatic cliques for a two-colouring -/

variable {α : Type*} [DecidableEq α] {c : α → α → Bool} {x : Bool}

/-- `S` is a monochromatic clique of colour `x` for the two-colouring `c`. -/

lemma ramsey_4_4_upper (hsym : ∀ a b, c a b = c b a) {V : Finset α} (hV : 18 ≤ V.card) :
    ∃ S ⊆ V, S.card = 4 ∧ (MonoClique c true S ∨ MonoClique c false S) := by
  obtain ⟨W, hWV, hW⟩ := Finset.exists_subset_card_eq hV
  have hne : W.Nonempty := by
    rw [← Finset.card_pos, hW]; norm_num
  obtain ⟨v, hvW⟩ := hne
  have hsplit := card_redN_add_card_blueN (c := c) hvW
  rw [hW] at hsplit
  by_cases h : 9 ≤ (redN c W v).card
  · obtain ⟨T, hTsub, hT9⟩ := Finset.exists_subset_card_eq h
    have hTW : T ⊆ W := hTsub.trans (redN_subset.trans (Finset.erase_subset _ _))
    rcases ramsey_3_4 (c := c) hsym hT9.ge with ⟨S, hST, hS3, hS⟩ | ⟨S, hST, hS4, hS⟩
    · have hvS : v ∉ S := fun hvS => (Finset.mem_erase.1 (redN_subset (hTsub (hST hvS)))).1 rfl
      refine ⟨insert v S, Finset.insert_subset (hWV hvW) ((hST.trans hTW).trans hWV), ?_,
        Or.inl (monoClique_insert hsym hS (fun u hu => (mem_redN.1 (hTsub (hST hu))).2))⟩
      rw [Finset.card_insert_of_notMem hvS, hS3]
    · exact ⟨S, (hST.trans hTW).trans hWV, hS4, Or.inr hS⟩
  · obtain ⟨T, hTsub, hT9⟩ := Finset.exists_subset_card_eq
      (show 9 ≤ (blueN c W v).card by omega)
    have hTW : T ⊆ W := hTsub.trans (blueN_subset.trans (Finset.erase_subset _ _))
    rcases ramsey_4_3 (c := c) hsym hT9.ge with ⟨S, hST, hS4, hS⟩ | ⟨S, hST, hS3, hS⟩
    · exact ⟨S, (hST.trans hTW).trans hWV, hS4, Or.inl hS⟩
    · have hvS : v ∉ S := fun hvS => (Finset.mem_erase.1 (blueN_subset (hTsub (hST hvS)))).1 rfl
      refine ⟨insert v S, Finset.insert_subset (hWV hvW) ((hST.trans hTW).trans hWV), ?_,
        Or.inr (monoClique_insert hsym hS (fun u hu => (mem_blueN.1 (hTsub (hST hu))).2))⟩
      rw [Finset.card_insert_of_notMem hvS, hS3]

/-! ## The Ramsey property and the main theorem -/

/-- Every symmetric two-colouring of the edges of the complete graph on `n` vertices
contains a monochromatic clique on `4` vertices. -/
