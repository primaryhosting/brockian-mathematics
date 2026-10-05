import Mathlib
/-!
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

open Finset

/-! ## Upper bound: every 2-colouring of `K₁₈` has a monochromatic `K₄`

We phrase a 2-colouring of the edges of a complete graph as a simple graph `G`
(the "red" edges); the "blue" edges are the edges of the complement `Gᶜ`.
-/

section Core

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The neighbours of `v` inside the finite set `s`. -/

lemma exists_r44 {s : Finset V} (hs : 18 ≤ s.card) :
    (∃ t ⊆ s, G.IsNClique 4 t) ∨ (∃ t ⊆ s, Gᶜ.IsNClique 4 t) := by
  obtain ⟨v, hv⟩ : s.Nonempty := Finset.card_pos.mp (by omega)
  have hpart := card_nb_add_card_nb_compl (G := G) hv
  by_cases hR : 9 ≤ (nb G s v).card
  · exact four_clique_of_nb hv hR
  · have hB : 9 ≤ (nb Gᶜ s v).card := by omega
    have := four_clique_of_nb (G := Gᶜ) hv hB
    rw [compl_compl] at this
    exact this.symm

end Core

/-! ## Lower bound: the Paley graph on 17 vertices

The Paley graph on `ZMod 17`: `i ~ j` iff `i - j` is a nonzero quadratic residue mod `17`,
i.e. lies in `{1,2,4,8,9,13,15,16}`.  Neither it nor its complement contains a `K₄`.
-/

/-- Membership test for the nonzero quadratic residues modulo `17`. -/
