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

lemma triangle_of_nb {s : Finset V} {v : V} (hv : v ∈ s) (h3 : 3 ≤ (nb G s v).card) :
    (∃ t ⊆ s, G.IsNClique 3 t) ∨ (∃ t ⊆ s, Gᶜ.IsNClique 3 t) := by
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq h3
  by_cases hcl : Gᶜ.IsClique (t : Set V)
  · exact Or.inr ⟨t, hts.trans (nb_subset s v), hcl, htc⟩
  · rw [SimpleGraph.isClique_iff, Set.Pairwise] at hcl
    push_neg at hcl
    obtain ⟨x, hx, y, hy, hxy, hadj⟩ := hcl
    simp only [Finset.mem_coe] at hx hy
    have hax : G.Adj v x := (mem_nb.mp (hts hx)).2
    have hay : G.Adj v y := (mem_nb.mp (hts hy)).2
    refine Or.inl ⟨{v, x, y}, ?_, ?_⟩
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact hv
      · exact (nb_subset s v) (hts hx)
      · exact (nb_subset s v) (hts hy)
    · exact SimpleGraph.is3Clique_triple_iff.mpr ⟨hax, hay, adj_of_not_compl_adj hxy hadj⟩

omit [Fintype V] in
/-- `R(3,3) ≤ 6`. -/
