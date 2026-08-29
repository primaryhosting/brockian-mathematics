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

lemma ramsey_44_le [LinearOrder V] (hsym : ∀ x y, f x y = f y x) (W : Finset V)
    (hW : 18 ≤ W.card) : ∃ S ⊆ W, S.card = 4 ∧ (MonoSet f true S ∨ MonoSet f false S) := by
  obtain ⟨W', hW'W, hW'⟩ := Finset.le_card_iff_exists_subset_card.mp hW
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < W'.card by omega)
  have hc := card_nbr_add (f := f) hv
  rcases (show 9 ≤ (nbr f true W' v).card ∨ 9 ≤ (nbr f false W' v).card by omega) with h9 | h9
  · obtain ⟨S, hSA, h⟩ := ramsey_34 hsym (nbr f true W' v) h9
    rcases h with ⟨hcard, hm⟩ | ⟨hcard, hm⟩
    · obtain ⟨h1, h2, h3⟩ := mono_insert hsym hv hSA hm
      exact ⟨insert v S, h1.trans hW'W, by rw [h2, hcard], Or.inl h3⟩
    · exact ⟨S, (hSA.trans nbr_subset).trans hW'W, hcard, Or.inr hm⟩
  · obtain ⟨S, hSA, h⟩ := ramsey_43 hsym (nbr f false W' v) h9
    rcases h with ⟨hcard, hm⟩ | ⟨hcard, hm⟩
    · exact ⟨S, (hSA.trans nbr_subset).trans hW'W, hcard, Or.inl hm⟩
    · obtain ⟨h1, h2, h3⟩ := mono_insert hsym hv hSA hm
      exact ⟨insert v S, h1.trans hW'W, by rw [h2, hcard], Or.inr h3⟩

end General

/-! ### The lower bound: the Paley graph of order 17 -/

/-- `qr n` decides whether `n % 17` is a nonzero quadratic residue modulo `17`.
The residues are `1, 2, 4, 8, 9, 13, 15, 16`, encoded as the bit mask `107286`. -/
