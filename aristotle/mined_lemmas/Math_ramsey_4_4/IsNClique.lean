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
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Math

open Finset

/-- `RamseyProp N p q` says: for every red/blue colouring of the edges of a complete graph
(the red edges being the edges of a simple graph `G`), every set `t` of at least `N` vertices
contains a red clique of size `p` or a blue clique of size `q`.
Here "blue" means an edge of the complement `Gᶜ`. -/

theorem IsNClique.comap_image {V W : Type} [DecidableEq V] [DecidableEq W] {k : ℕ} (f : V ↪ W)
    (G : SimpleGraph W) {s : Finset V} (h : (SimpleGraph.comap f G).IsNClique k s) :
    G.IsNClique k (s.image f) := by
  constructor
  · intro x hx y hy hxy
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact h.1 (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) (fun hab => hxy (by rw [hab]))
  · rw [Finset.card_image_of_injective _ f.injective, h.2]

