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

lemma ramsey_3_4 (hsym : ∀ a b, c a b = c b a) {V : Finset α} (hV : 9 ≤ V.card) :
    (∃ S ⊆ V, S.card = 3 ∧ MonoClique c true S) ∨
      (∃ S ⊆ V, S.card = 4 ∧ MonoClique c false S) := by
  obtain ⟨W, hWV, hW⟩ := Finset.exists_subset_card_eq hV
  by_contra hcon
  push_neg at hcon
  obtain ⟨h3, h4⟩ := hcon
  have key3 : ∀ S ⊆ W, S.card = 3 → ¬ MonoClique c true S := fun S hS => h3 S (hS.trans hWV)
  have key4 : ∀ S ⊆ W, S.card = 4 → ¬ MonoClique c false S := fun S hS => h4 S (hS.trans hWV)
  have hdeg : ∀ v ∈ W, (redN c W v).card = 3 := by
    intro v hv
    have hsplit := card_redN_add_card_blueN (c := c) hv
    rw [hW] at hsplit
    have hle : (redN c W v).card ≤ 3 := by
      by_contra hgt
      obtain ⟨T, hTsub, hT4⟩ := Finset.exists_subset_card_eq
        (show 4 ≤ (redN c W v).card by omega)
      rcases key_red hv hsym hTsub with ⟨S, hSW, hS3, hS⟩ | hTm
      · exact key3 S hSW hS3 hS
      · exact key4 T (hTsub.trans (redN_subset.trans (Finset.erase_subset _ _))) hT4 hTm
    have hge : 3 ≤ (redN c W v).card := by
      by_contra hlt
      obtain ⟨B, hBsub, hB6⟩ := Finset.exists_subset_card_eq
        (show 6 ≤ (blueN c W v).card by omega)
      have hBW : B ⊆ W := hBsub.trans (blueN_subset.trans (Finset.erase_subset _ _))
      obtain ⟨S, hSB, hS3, hS⟩ := ramsey_3_3 (c := c) hsym hB6.ge
      rcases hS with hS | hS
      · exact key3 S (hSB.trans hBW) hS3 hS
      · have hvS : v ∉ S := fun hvS =>
          (Finset.mem_erase.1 (blueN_subset (hBsub (hSB hvS)))).1 rfl
        refine key4 (insert v S) (Finset.insert_subset hv (hSB.trans hBW)) ?_
          (monoClique_insert hsym hS (fun u hu => (mem_blueN.1 (hBsub (hSB hu))).2))
        rw [Finset.card_insert_of_notMem hvS, hS3]
    omega
  have hsum : ∑ v ∈ W, (redN c W v).card = 27 := by
    rw [Finset.sum_congr rfl hdeg, Finset.sum_const, hW]
    norm_num
  have heven := even_sum_redDeg (c := c) hsym W
  rw [hsum] at heven
  exact (by decide : ¬ Even 27) heven

