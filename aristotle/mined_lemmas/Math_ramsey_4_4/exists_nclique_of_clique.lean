/-
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Math

open Finset SimpleGraph

/-- Extract four elements in increasing order from a four-element finset. -/

theorem exists_nclique_of_clique {G : SimpleGraph V} {S : Finset V} (hS : G.IsClique S) {n : ℕ}
    (hn : n ≤ S.card) : ∃ s ⊆ S, G.IsNClique n s := by
  obtain ⟨t, ht, hcard⟩ := Finset.exists_subset_card_eq hn
  exact ⟨t, ht, ⟨hS.subset (by exact_mod_cast ht), hcard⟩⟩

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The neighbours of `v` inside `T`. -/
