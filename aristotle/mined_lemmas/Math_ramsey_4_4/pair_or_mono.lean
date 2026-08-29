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

lemma pair_or_mono {b : Bool} {A : Finset V} {n : ℕ} (h : n ≤ A.card) :
    (∃ i ∈ A, ∃ j ∈ A, i ≠ j ∧ f i j = b) ∨ (∃ S ⊆ A, S.card = n ∧ MonoSet f (!b) S) := by
  by_cases hp : ∃ i ∈ A, ∃ j ∈ A, i ≠ j ∧ f i j = b
  · exact Or.inl hp
  · right
    push_neg at hp
    obtain ⟨S, hSA, hS⟩ := Finset.le_card_iff_exists_subset_card.mp h
    refine ⟨S, hSA, hS, fun i hi j hj hij => ?_⟩
    have := hp i (hSA hi) j (hSA hj) hij
    cases hb : f i j <;> cases b <;> simp_all

