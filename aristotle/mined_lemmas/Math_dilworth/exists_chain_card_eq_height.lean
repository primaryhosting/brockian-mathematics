/-
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Math

open scoped Classical in
/-- The maximal cardinality of a chain in a finite partial order. -/

lemma exists_chain_card_eq_height (x : α) :
    ∃ c : Finset α, IsChain (· ≤ ·) (c : Set α) ∧ (∀ y ∈ c, y ≤ x) ∧ c.card = height x := by
  classical
  obtain ⟨c, hc, hsup⟩ :=
    Finset.exists_mem_eq_sup
      (Finset.univ.filter
        (fun c : Finset α => IsChain (· ≤ ·) (c : Set α) ∧ ∀ y ∈ c, y ≤ x))
      ⟨∅, by simp⟩ Finset.card
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
  exact ⟨c, hc.1, hc.2, (hsup.symm : _)⟩

