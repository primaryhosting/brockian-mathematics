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

lemma card_nb_add_card_nb_compl {s : Finset V} {v : V} (hv : v ∈ s) :
    (nb G s v).card + (nb Gᶜ s v).card + 1 = s.card := by
  have h1 : nb G s v = (s.erase v).filter (fun u => G.Adj v u) := by
    ext u
    simp only [mem_nb, Finset.mem_filter, Finset.mem_erase]
    exact ⟨fun h => ⟨⟨(G.ne_of_adj h.2).symm, h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩
  have h2 : nb Gᶜ s v = (s.erase v).filter (fun u => ¬ G.Adj v u) := by
    ext u
    simp only [mem_nb, Finset.mem_filter, Finset.mem_erase, SimpleGraph.compl_adj]
    constructor
    · rintro ⟨hus, hne, hadj⟩
      exact ⟨⟨hne.symm, hus⟩, hadj⟩
    · rintro ⟨⟨hne, hus⟩, hadj⟩
      exact ⟨hus, hne.symm, hadj⟩
  have h3 := Finset.card_filter_add_card_filter_not (s := s.erase v) (fun u => G.Adj v u)
  rw [h1, h2]
  rw [h3, Finset.card_erase_of_mem hv]
  have : 1 ≤ s.card := Finset.card_pos.mpr ⟨v, hv⟩
  omega

omit [Fintype V] in
/-- If `v` has at least three neighbours inside `s`, then `s` contains a monochromatic triangle. -/
