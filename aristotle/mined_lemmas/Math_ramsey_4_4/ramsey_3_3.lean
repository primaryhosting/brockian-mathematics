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

lemma ramsey_3_3 (hsym : ∀ a b, c a b = c b a) {V : Finset α} (hV : 6 ≤ V.card) :
    ∃ S ⊆ V, S.card = 3 ∧ (MonoClique c true S ∨ MonoClique c false S) := by
  obtain ⟨W, hWV, hW⟩ := Finset.exists_subset_card_eq hV
  have hne : W.Nonempty := by
    rw [← Finset.card_pos, hW]; norm_num
  obtain ⟨v, hvW⟩ := hne
  have hsplit := card_redN_add_card_blueN (c := c) hvW
  rw [hW] at hsplit
  by_cases h : 3 ≤ (redN c W v).card
  · obtain ⟨T, hTsub, hT3⟩ := Finset.exists_subset_card_eq h
    have hTW : T ⊆ W := hTsub.trans (redN_subset.trans (Finset.erase_subset _ _))
    rcases key_red hvW hsym hTsub with ⟨S, hSW, hS3, hS⟩ | hTm
    · exact ⟨S, hSW.trans hWV, hS3, Or.inl hS⟩
    · exact ⟨T, hTW.trans hWV, hT3, Or.inr hTm⟩
  · have hb : 3 ≤ (blueN c W v).card := by omega
    obtain ⟨T, hTsub, hT3⟩ := Finset.exists_subset_card_eq hb
    have hTW : T ⊆ W := hTsub.trans (blueN_subset.trans (Finset.erase_subset _ _))
    rcases key_blue hvW hsym hTsub with ⟨S, hSW, hS3, hS⟩ | hTm
    · exact ⟨S, hSW.trans hWV, hS3, Or.inr hS⟩
    · exact ⟨T, hTW.trans hWV, hT3, Or.inl hTm⟩

/-! ## R(3,4) ≤ 9 -/

