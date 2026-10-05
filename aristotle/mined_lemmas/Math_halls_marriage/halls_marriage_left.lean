import Mathlib

/-!
# Halls Marriage
Category: Pure Mathematics
Target: Math.halls_marriage
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A matching `M` of a graph `G` gives, for every matched vertex `v`, a neighbour
`matchedVertex M v` of `v` in `G`, and this assignment is injective on the matched vertices. -/

theorem halls_marriage_left [Fintype V] [DecidableRel G.Adj] {p₁ p₂ : Set V}
    (hG : G.IsBipartiteWith p₁ p₂) :
    (∃ M : G.Subgraph, p₁ ⊆ M.verts ∧ M.IsMatching) ↔
      ∀ s ⊆ p₁, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard := by
  constructor
  · rintro ⟨M, hMv, hM⟩ s hs
    exact ncard_le_ncard_biUnion_neighborSet_of_isMatching hM (hs.trans hMv)
  · intro h
    exact SimpleGraph.exists_isMatching_of_forall_ncard_le hG h

end Math

