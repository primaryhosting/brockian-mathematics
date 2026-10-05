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
noncomputable def matchedVertex (M : G.Subgraph) (v : V) : V :=
  if h : ∃ w, M.Adj v w then h.choose else v

lemma adj_matchedVertex {M : G.Subgraph} {v : V} (hv : v ∈ M.verts) (hM : M.IsMatching) :
    M.Adj v (matchedVertex M v) := by
  obtain ⟨w, hw, -⟩ := hM hv
  have h : ∃ w, M.Adj v w := ⟨w, hw⟩
  rw [matchedVertex, dif_pos h]
  exact h.choose_spec

lemma injOn_matchedVertex {M : G.Subgraph} (hM : M.IsMatching) :
    Set.InjOn (matchedVertex M) M.verts := by
  intro x hx y hy hxy
  have hax : M.Adj x (matchedVertex M x) := adj_matchedVertex hx hM
  have hay : M.Adj y (matchedVertex M y) := adj_matchedVertex hy hM
  have hw : matchedVertex M x ∈ M.verts := M.edge_vert hax.symm
  obtain ⟨z, -, hz⟩ := hM hw
  have h1 : x = z := hz x hax.symm
  have h2 : y = z := hz y (by rw [hxy]; exact hay.symm)
  rw [h1, h2]

/-- **Hall's condition** holds for a set of matched vertices: for every subset `s` of the
matched vertices, `s` has at least `s.ncard` neighbours in `G`. -/
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
theorem halls_marriage [Fintype V] [DecidableRel G.Adj] {p₁ p₂ : Set V}
    (hG : G.IsBipartiteWith p₁ p₂) :
    (∃ M : G.Subgraph, M.IsPerfectMatching) ↔
      ∀ s : Set V, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard := by
  constructor
  · rintro ⟨M, hM⟩ s
    exact ncard_le_ncard_biUnion_neighborSet_of_isMatching hM.1
      (fun x _ => hM.2 x)
  · intro h
    exact SimpleGraph.exists_isPerfectMatching_of_forall_ncard_le hG h

/-- **Hall's marriage theorem** for bipartite graphs, in the form saturating one part:
there is a matching covering the part `p₁` if and only if Hall's condition holds for all
subsets of `p₁`. -/
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

