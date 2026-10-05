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

lemma even_sum_deg [LinearOrder V] (hsym : ∀ x y, f x y = f y x) (W : Finset V) :
    Even (∑ v ∈ W, (nbr f true W v).card) := by
  classical
  set P : Finset (V × V) := {p ∈ W ×ˢ W | p.1 ≠ p.2 ∧ f p.1 p.2 = true} with hP
  have hnb : ∀ v, nbr f true W v = {u ∈ W | v ≠ u ∧ f v u = true} := by
    intro v
    ext u
    simp only [nbr, Finset.mem_filter, Finset.mem_erase]
    tauto
  have key : ∑ v ∈ W, (nbr f true W v).card = P.card := by
    rw [hP, Finset.card_filter, Finset.sum_product]
    exact Finset.sum_congr rfl fun v _ => by rw [hnb v, Finset.card_filter]
  have hsplit := Finset.card_filter_add_card_filter_not (s := P) (p := fun p : V × V => p.1 < p.2)
  have hmemP : ∀ p : V × V, p ∈ P ↔ (p.1 ∈ W ∧ p.2 ∈ W ∧ p.1 ≠ p.2 ∧ f p.1 p.2 = true) := by
    intro p
    simp only [hP, Finset.mem_filter, Finset.mem_product]
    tauto
  have hbij : ({p ∈ P | p.1 < p.2}).card = ({p ∈ P | ¬ p.1 < p.2}).card := by
    refine Finset.card_bij' (fun p _ => (p.2, p.1)) (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, hmemP] at hp ⊢
      obtain ⟨⟨h1, h2, hne, hf⟩, hlt⟩ := hp
      exact ⟨⟨h2, h1, hne.symm, by rw [hsym]; exact hf⟩, by simpa using le_of_lt hlt⟩
    · intro p hp
      simp only [Finset.mem_filter, hmemP] at hp ⊢
      obtain ⟨⟨h1, h2, hne, hf⟩, hlt⟩ := hp
      exact ⟨⟨h2, h1, hne.symm, by rw [hsym]; exact hf⟩,
        lt_of_le_of_ne (not_lt.mp hlt) hne.symm⟩
    · intro p _; rfl
    · intro p _; rfl
  have hP2 : P.card = 2 * ({p ∈ P | p.1 < p.2}).card := by omega
  rw [key, hP2]
  exact even_two_mul _

/-- If some vertex `v` of `W` has at least three `b`-coloured neighbours in `W`, then `W`
contains a monochromatic triangle. -/
