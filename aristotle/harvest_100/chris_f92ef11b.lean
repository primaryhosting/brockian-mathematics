/-
# Halls Marriage
Category: Pure Mathematics
Target: Math.halls_marriage
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Halls Marriage
Category: Pure Mathematics
Target: Math.halls_marriage
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- The *Hall condition* for a graph `G`: every set of vertices `s` has at least as many
neighbours (counted in the union of the neighbourhoods of its elements) as it has elements. -/
def HallCondition (G : SimpleGraph V) : Prop :=
  ∀ s : Set V, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard

/-- The neighbourhood of a finite set of vertices in a locally finite graph is finite. -/
lemma finite_biUnion_neighborSet [G.LocallyFinite] {s : Set V} (hs : s.Finite) :
    (⋃ x ∈ s, G.neighborSet x).Finite :=
  hs.biUnion fun x _ => Set.toFinite (G.neighborSet x)

/-- A matching `M` yields an injection from its vertex set into the graph's vertices which
sends each vertex to one of its neighbours. -/
lemma ncard_le_ncard_biUnion_neighborSet_of_isMatching [G.LocallyFinite] {M : G.Subgraph}
    (hM : M.IsMatching) {s : Set V} (hs : s ⊆ M.verts) :
    s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard := by
  classical
  rcases s.finite_or_infinite with hfin | hinf
  · -- pick the matched partner of each vertex
    choose f hf hf' using fun (v : V) (hv : v ∈ M.verts) => hM hv
    set g : V → V := fun v => if hv : v ∈ M.verts then f v hv else v with hg
    have hmaps : ∀ a ∈ s, g a ∈ ⋃ x ∈ s, G.neighborSet x := by
      intro a ha
      have haM : a ∈ M.verts := hs ha
      have : M.Adj a (g a) := by simp only [hg, dif_pos haM]; exact hf a haM
      exact Set.mem_biUnion ha (M.adj_sub this)
    have hinj : Set.InjOn g s := by
      intro a ha b hb hab
      have haM : a ∈ M.verts := hs ha
      have hbM : b ∈ M.verts := hs hb
      have ha' : M.Adj a (g a) := by simp only [hg, dif_pos haM]; exact hf a haM
      have hb' : M.Adj b (g b) := by simp only [hg, dif_pos hbM]; exact hf b hbM
      -- `g a = g b` is adjacent to both `a` and `b`, and its partner is unique
      have hc : g a ∈ M.verts := M.edge_vert ha'.symm
      have h1 : M.Adj (g a) a := ha'.symm
      have h2 : M.Adj (g a) b := hab ▸ hb'.symm
      obtain ⟨w, _, hw⟩ := hM hc
      exact (hw a h1).trans (hw b h2).symm
    exact Set.ncard_le_ncard_of_injOn g hmaps hinj (finite_biUnion_neighborSet hfin)
  · simp [hinf.ncard]

/-- **Hall's marriage theorem** for bipartite graphs: a (locally finite) bipartite graph has a
perfect matching if and only if Hall's condition holds, i.e. every set of vertices `s` satisfies
`|s| ≤ |N(s)|`. -/
theorem halls_marriage [G.LocallyFinite] {p₁ p₂ : Set V} (h : G.IsBipartiteWith p₁ p₂) :
    (∃ M : G.Subgraph, M.IsPerfectMatching) ↔ HallCondition G := by
  constructor
  · rintro ⟨M, hM⟩ s
    exact ncard_le_ncard_biUnion_neighborSet_of_isMatching hM.1
      (fun v _ => hM.2 v)
  · intro hH
    exact SimpleGraph.exists_isPerfectMatching_of_forall_ncard_le h hH

/-- **Hall's marriage theorem**, one-sided version: a locally finite bipartite graph with parts
`p₁`, `p₂` has a matching saturating `p₁` if and only if `|s| ≤ |N(s)|` for every `s ⊆ p₁`. -/
theorem halls_marriage_saturating [G.LocallyFinite] {p₁ p₂ : Set V} (h : G.IsBipartiteWith p₁ p₂) :
    (∃ M : G.Subgraph, p₁ ⊆ M.verts ∧ M.IsMatching) ↔
      ∀ s ⊆ p₁, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard := by
  constructor
  · rintro ⟨M, hsub, hM⟩ s hs
    exact ncard_le_ncard_biUnion_neighborSet_of_isMatching hM (hs.trans hsub)
  · intro hH
    exact SimpleGraph.exists_isMatching_of_forall_ncard_le h hH

end Math

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

