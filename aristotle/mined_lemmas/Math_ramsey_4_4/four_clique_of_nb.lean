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

lemma four_clique_of_nb {s : Finset V} {v : V} (hv : v ∈ s) (h9 : 9 ≤ (nb G s v).card) :
    (∃ t ⊆ s, G.IsNClique 4 t) ∨ (∃ t ⊆ s, Gᶜ.IsNClique 4 t) := by
  rcases exists_r34 (G := G) h9 with ⟨t, ht, h3⟩ | ⟨t, ht, h4⟩
  · refine Or.inl ⟨insert v t, Finset.insert_subset hv (ht.trans (nb_subset s v)), ?_⟩
    exact h3.insert (fun b hb => (mem_nb.mp (ht hb)).2)
  · exact Or.inr ⟨t, ht.trans (nb_subset s v), h4⟩

/-- `R(4,4) ≤ 18`. -/
