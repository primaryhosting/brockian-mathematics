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

lemma ramsey_43 [LinearOrder V] (hsym : ∀ x y, f x y = f y x) (W : Finset V) (hW : 9 ≤ W.card) :
    ∃ S ⊆ W, (S.card = 4 ∧ MonoSet f true S) ∨ (S.card = 3 ∧ MonoSet f false S) := by
  have hsym' : ∀ x y, (!f x y) = (!f y x) := fun x y => by rw [hsym]
  obtain ⟨S, hSW, h⟩ := ramsey_34 (f := fun i j => !f i j) hsym' W hW
  refine ⟨S, hSW, ?_⟩
  rcases h with ⟨hc, hm⟩ | ⟨hc, hm⟩
  · exact Or.inr ⟨hc, mono_flip.mp hm⟩
  · exact Or.inl ⟨hc, mono_flip.mp hm⟩

/-- `R(4,4) ≤ 18`. -/
