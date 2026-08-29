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

lemma exists_mono_three {s : Finset V} (hs : 6 ≤ s.card) :
    (∃ t ⊆ s, G.IsNClique 3 t) ∨ (∃ t ⊆ s, Gᶜ.IsNClique 3 t) := by
  obtain ⟨v, hv⟩ : s.Nonempty := Finset.card_pos.mp (by omega)
  have hpart := card_nb_add_card_nb_compl (G := G) hv
  by_cases hR : 3 ≤ (nb G s v).card
  · exact triangle_of_nb hv hR
  · have hB : 3 ≤ (nb Gᶜ s v).card := by omega
    have := triangle_of_nb (G := Gᶜ) hv hB
    rw [compl_compl] at this
    exact this.symm

/-- `R(3,4) ≤ 9`: nine vertices contain a red triangle or a blue `K₄`. -/
