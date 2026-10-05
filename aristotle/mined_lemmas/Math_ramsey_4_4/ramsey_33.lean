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

lemma ramsey_33 (hsym : ∀ x y, f x y = f y x) (W : Finset V) (hW : 6 ≤ W.card) :
    ∃ S ⊆ W, S.card = 3 ∧ (MonoSet f true S ∨ MonoSet f false S) := by
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < W.card by omega)
  have h := card_nbr_add (f := f) hv
  rcases (show 3 ≤ (nbr f true W v).card ∨ 3 ≤ (nbr f false W v).card by omega) with h3 | h3
  · exact triple_of_three hsym hv h3
  · exact triple_of_three hsym hv h3

/-- `R(3,4) ≤ 9`. -/
