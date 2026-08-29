/-
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 4 4

We show that the two-colour Ramsey number `R(4,4)` equals `18`:

* every symmetric two-colouring of the edges of the complete graph on `18` vertices
  contains a monochromatic set of `4` vertices;
* there is a symmetric two-colouring of the edges of the complete graph on `17` vertices
  (the Paley graph of order `17`) with no monochromatic set of `4` vertices.
-/

namespace Math

open Finset

/-- `MonoSet f b S` says that every pair of distinct vertices of `S` receives colour `b`. -/

lemma ramsey_34 [LinearOrder V] (hsym : ∀ x y, f x y = f y x) (W : Finset V) (hW : 9 ≤ W.card) :
    ∃ S ⊆ W, (S.card = 3 ∧ MonoSet f true S) ∨ (S.card = 4 ∧ MonoSet f false S) := by
  obtain ⟨W', hW'W, hW'⟩ := Finset.le_card_iff_exists_subset_card.mp hW
  suffices h : ∃ S ⊆ W', (S.card = 3 ∧ MonoSet f true S) ∨ (S.card = 4 ∧ MonoSet f false S) by
    obtain ⟨S, hS, h⟩ := h
    exact ⟨S, hS.trans hW'W, h⟩
  by_contra hcon
  have hno : ∀ S, S ⊆ W' →
      ¬((S.card = 3 ∧ MonoSet f true S) ∨ (S.card = 4 ∧ MonoSet f false S)) :=
    fun S hS h => hcon ⟨S, hS, h⟩
  -- no vertex has four `true`-neighbours
  have hv3 : ∀ v ∈ W', (nbr f true W' v).card ≤ 3 := by
    intro v hv
    by_contra hgt
    push_neg at hgt
    rcases pair_or_mono (b := true) (n := 4) (show 4 ≤ (nbr f true W' v).card by omega) with
      ⟨i, hi, j, hj, hij, hfij⟩ | ⟨S, hSA, hc, hm⟩
    · obtain ⟨h1, h2, h3⟩ := mono_insert hsym hv
        (Finset.insert_subset hi (Finset.singleton_subset_iff.mpr hj)) (mono_pair hsym hfij)
      exact hno _ h1 (Or.inl ⟨by rw [h2, Finset.card_pair hij], h3⟩)
    · exact hno S (hSA.trans nbr_subset) (Or.inr ⟨hc, hm⟩)
  -- no vertex has six `false`-neighbours
  have hv5 : ∀ v ∈ W', (nbr f false W' v).card ≤ 5 := by
    intro v hv
    by_contra hgt
    push_neg at hgt
    obtain ⟨S, hSA, hc, hm⟩ := ramsey_33 hsym (nbr f false W' v) (by omega)
    rcases hm with hm | hm
    · exact hno S (hSA.trans nbr_subset) (Or.inl ⟨hc, hm⟩)
    · obtain ⟨h1, h2, h3⟩ := mono_insert hsym hv hSA hm
      exact hno _ h1 (Or.inr ⟨by rw [h2, hc], h3⟩)
  -- hence the `true` graph is 3-regular on nine vertices, contradicting the handshake lemma
  have hdeg : ∀ v ∈ W', (nbr f true W' v).card = 3 := by
    intro v hv
    have h := card_nbr_add (f := f) hv
    have h3 := hv3 v hv
    have h5 := hv5 v hv
    omega
  have hsum : ∑ v ∈ W', (nbr f true W' v).card = 27 := by
    rw [Finset.sum_congr rfl hdeg]
    simp [hW']
  have heven := even_sum_deg hsym W'
  rw [hsum] at heven
  exact (by decide : ¬ Even 27) heven

/-- `R(4,3) ≤ 9`. -/
