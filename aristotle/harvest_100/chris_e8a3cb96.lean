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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math

open SimpleGraph

/-- The union of the neighborhoods of a finite vertex set is finite in a locally finite graph. -/
lemma finite_biUnion_neighborSet {V : Type*} (G : SimpleGraph V) [G.LocallyFinite]
    {s : Set V} (hs : s.Finite) : (⋃ x ∈ s, G.neighborSet x).Finite :=
  hs.biUnion fun x _ => Set.toFinite (G.neighborSet x)

/-- If a graph has a perfect matching, then Hall's condition holds: every set of vertices
has a neighborhood at least as large. -/
lemma forall_ncard_le_of_isPerfectMatching {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
    {M : G.Subgraph} (hM : M.IsPerfectMatching) (s : Set V) :
    s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard := by
  classical
  rcases Set.finite_or_infinite s with hs | hs
  · -- the matching partner function
    have hex : ∀ v : V, ∃! w, M.Adj v w := Subgraph.isPerfectMatching_iff.mp hM
    set g : V → V := fun v => (hex v).choose
    have hgadj : ∀ v : V, M.Adj v (g v) := fun v => (hex v).choose_spec.1
    have hginj : Function.Injective g := by
      intro u v huv
      have hu : M.Adj (g u) u := (hgadj u).symm
      have hv : M.Adj (g u) v := huv ▸ (hgadj v).symm
      exact ((hex (g u)).unique hu hv)
    have hsub : g '' s ⊆ ⋃ x ∈ s, G.neighborSet x := by
      rintro _ ⟨x, hx, rfl⟩
      exact Set.mem_biUnion hx (M.adj_sub (hgadj x))
    have hfin : (⋃ x ∈ s, G.neighborSet x).Finite := finite_biUnion_neighborSet G hs
    calc s.ncard = (g '' s).ncard :=
          (Set.ncard_image_of_injective s hginj).symm
      _ ≤ (⋃ x ∈ s, G.neighborSet x).ncard := Set.ncard_le_ncard hsub hfin
  · simp [hs.ncard]

/-- **Hall's Marriage Theorem** for bipartite graphs.

A locally finite bipartite graph `G` with parts `p₁`, `p₂` has a perfect matching if and only if
Hall's condition holds, i.e. every set of vertices `s` satisfies `s.ncard ≤ (⋃ x ∈ s, N(x)).ncard`.

The `←` direction is `SimpleGraph.exists_isPerfectMatching_of_forall_ncard_le` from Mathlib
(`Mathlib/Combinatorics/SimpleGraph/Hall.lean`), which is in turn bootstrapped from the
combinatorial form `Finset.all_card_le_biUnion_card_iff_exists_injective`.  The `→` direction is
proved here; it does not actually need the bipartiteness hypothesis, which is retained only
because the statement is about bipartite graphs. -/
theorem halls_marriage {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {p₁ p₂ : Set V}
    (hG : G.IsBipartiteWith p₁ p₂) :
    (∃ M : G.Subgraph, M.IsPerfectMatching) ↔
      ∀ s : Set V, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard := by
  constructor
  · rintro ⟨M, hM⟩
    exact forall_ncard_le_of_isPerfectMatching hM
  · intro h
    exact SimpleGraph.exists_isPerfectMatching_of_forall_ncard_le hG h

end Math
#print axioms Math.halls_marriage

