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

namespace Math

open Finset SimpleGraph

/-! ### Generic clique helpers -/

section Helpers
variable {V : Type*} {G : SimpleGraph V}

/-- A set with no internal `G`-edges is a clique of the complement. -/

lemma exists_isNClique_of_induce {s : Set V} {n : ℕ} {t : Finset s}
    (ht : (G.induce s).IsNClique n t) :
    ∃ u : Finset V, (∀ x ∈ u, x ∈ s) ∧ G.IsNClique n u := by
  refine ⟨t.map (Function.Embedding.subtype _), ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  · exact (ht.map (f := Function.Embedding.subtype _)).mono (SimpleGraph.map_comap_le _ _)

end Helpers

/-! ### The upper bound `R(4,4) ≤ 18` -/

section UpperBound
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Neighbours of `v`. -/
