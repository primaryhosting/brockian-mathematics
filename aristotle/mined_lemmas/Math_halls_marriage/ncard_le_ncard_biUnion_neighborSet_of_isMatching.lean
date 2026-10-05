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

lemma ncard_le_ncard_biUnion_neighborSet_of_isMatching [Finite V] {M : G.Subgraph}
    (hM : M.IsMatching) {s : Set V} (hs : s ⊆ M.verts) :
    s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard := by
  refine Set.ncard_le_ncard_of_injOn (matchedVertex M) (fun x hx => ?_)
    ((injOn_matchedVertex hM).mono hs) (Set.toFinite _)
  have hax : M.Adj x (matchedVertex M x) := adj_matchedVertex (hs hx) hM
  exact Set.mem_biUnion hx (M.adj_sub hax)

/-- **Hall's marriage theorem** for bipartite graphs, in the form of an equivalence:
a (finite) bipartite graph `G` with parts `p₁` and `p₂` has a perfect matching if and only if
Hall's condition holds, i.e. every set `s` of vertices has at least `s.ncard` neighbours. -/
