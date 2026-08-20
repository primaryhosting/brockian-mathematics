/-!
# Halls Marriage
Category: Pure Mathematics
Target: Math.halls_marriage
Statement: A bipartite graph has a perfect matching iff Hall's condition holds.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Math

open Function SimpleGraph

/-- From a perfect matching one extracts a partner function: an involution-free choice of
the unique `M`-neighbour of each vertex. -/
theorem exists_injective_partner_of_isPerfectMatching {V : Type*} {G : SimpleGraph V}
    {M : G.Subgraph} (hM : M.IsPerfectMatching) :
    ∃ f : V → V, Function.Injective f ∧ ∀ v, G.Adj v (f v) := by
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff] at hM
  choose f hf huniq using hM
  refine ⟨f, ?_, fun v => M.adj_sub (hf v)⟩
  intro v w hvw
  have hv : M.Adj (f v) v := (hf v).symm
  have hw : M.Adj (f v) w := hvw ▸ (hf w).symm
  have h1 := huniq (f v) v hv
  have h2 := huniq (f v) w hw
  exact h1.trans h2.symm

/-- A matching saturating a set `s` yields an injective map sending each vertex of `s` to an
adjacent vertex. -/
theorem exists_injOn_partner_of_isMatching {V : Type*} {G : SimpleGraph V}
    {M : G.Subgraph} (hM : M.IsMatching) {s : Set V} (hs : s ⊆ M.verts) :
    ∃ f : V → V, Set.InjOn f s ∧ ∀ v ∈ s, G.Adj v (f v) := by
  classical
  have key : ∀ v ∈ s, ∃ w, M.Adj v w ∧ ∀ y, M.Adj v y → y = w := by
    intro v hv
    obtain ⟨w, hw, huniq⟩ := hM (hs hv)
    exact ⟨w, hw, huniq⟩
  choose! f hf huniq using key
  refine ⟨f, ?_, fun v hv => M.adj_sub (hf v hv)⟩
  intro v hv w hw hvw
  have hv' : M.Adj (f v) v := (hf v hv).symm
  have hw' : M.Adj (f v) w := hvw ▸ (hf w hw).symm
  have hfv : f v ∈ M.verts := M.edge_vert hv'
  obtain ⟨u, _, hu⟩ := hM hfv
  rw [hu v hv', hu w hw']

/-- **Hall's Marriage Theorem** for bipartite graphs.

Let `G` be a bipartite graph on a finite vertex type, with parts `p₁` and `p₂`.
Then `G` admits a perfect matching if and only if Hall's condition holds, i.e. every set `s`
of vertices has at least as many neighbours as it has elements. -/
theorem halls_marriage {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {p₁ p₂ : Set V} (hbip : G.IsBipartiteWith p₁ p₂) :
    (∃ M : G.Subgraph, M.IsPerfectMatching) ↔
      ∀ s : Set V, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard := by
  constructor
  · rintro ⟨M, hM⟩ s
    obtain ⟨f, hinj, hadj⟩ := exists_injective_partner_of_isPerfectMatching hM
    refine Set.ncard_le_ncard_of_injOn f (fun x hx => ?_) (hinj.injOn) (Set.toFinite _)
    exact Set.mem_biUnion hx (hadj x)
  · intro h
    exact SimpleGraph.exists_isPerfectMatching_of_forall_ncard_le hbip h

/-- **Hall's Marriage Theorem**, one-sided version: a bipartite graph has a matching saturating
the part `p₁` if and only if Hall's condition holds for all subsets of `p₁`. -/
theorem halls_marriage_saturating {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {p₁ p₂ : Set V} (hbip : G.IsBipartiteWith p₁ p₂) :
    (∃ M : G.Subgraph, p₁ ⊆ M.verts ∧ M.IsMatching) ↔
      ∀ s ⊆ p₁, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard := by
  constructor
  · rintro ⟨M, hverts, hM⟩ s hs
    obtain ⟨f, hinj, hadj⟩ := exists_injOn_partner_of_isMatching hM (hs.trans hverts)
    refine Set.ncard_le_ncard_of_injOn f (fun x hx => ?_) hinj (Set.toFinite _)
    exact Set.mem_biUnion hx (hadj x hx)
  · intro h
    exact SimpleGraph.exists_isMatching_of_forall_ncard_le hbip h

end Math

