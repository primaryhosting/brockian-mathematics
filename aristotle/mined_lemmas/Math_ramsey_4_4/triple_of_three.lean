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

lemma triple_of_three (hsym : ∀ x y, f x y = f y x) {W : Finset V} {v : V} {b : Bool}
    (hv : v ∈ W) (h : 3 ≤ (nbr f b W v).card) :
    ∃ S ⊆ W, S.card = 3 ∧ (MonoSet f true S ∨ MonoSet f false S) := by
  rcases pair_or_mono (b := b) (n := 3) h with ⟨i, hi, j, hj, hij, hfij⟩ | ⟨S, hSA, hc, hm⟩
  · obtain ⟨h1, h2, h3⟩ := mono_insert hsym hv
      (Finset.insert_subset hi (Finset.singleton_subset_iff.mpr hj)) (mono_pair hsym hfij)
    exact ⟨insert v {i, j}, h1, by rw [h2, Finset.card_pair hij], mono_or h3⟩
  · exact ⟨S, hSA.trans nbr_subset, hc, mono_or hm⟩

/-- `R(3,3) ≤ 6`. -/
