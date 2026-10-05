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

lemma card_nbr_add {W : Finset V} {v : V} (hv : v ∈ W) :
    (nbr f true W v).card + (nbr f false W v).card + 1 = W.card := by
  have h2 : nbr f false W v = {u ∈ W.erase v | ¬ (f v u = true)} := by
    apply Finset.filter_congr
    intro u _
    simp
  have h1 := Finset.card_filter_add_card_filter_not (s := W.erase v) (p := fun u => f v u = true)
  rw [nbr, h2, h1, Finset.card_erase_of_mem hv]
  have : 1 ≤ W.card := Finset.card_pos.mpr ⟨v, hv⟩
  omega

/-- Adding `v` to a `b`-monochromatic subset of its `b`-neighbourhood keeps it
`b`-monochromatic. -/
