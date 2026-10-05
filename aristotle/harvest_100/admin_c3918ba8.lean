/-
# Halls Marriage
Category: Pure Mathematics
Target: Math.halls_marriage
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any command, including module docstrings, so the
-- header above is a plain comment and is repeated as the module docstring below.)

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

/-- Any perfect matching of a locally finite graph witnesses Hall's condition:
every set of vertices has at least as many vertices as its cardinality in its neighbourhood. -/
theorem ncard_le_ncard_biUnion_neighborSet_of_isPerfectMatching
    [G.LocallyFinite] {M : G.Subgraph} (hM : M.IsPerfectMatching) (s : Set V) :
    s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard := by
  classical
  rcases s.finite_or_infinite with hs | hs
  · rw [SimpleGraph.Subgraph.isPerfectMatching_iff] at hM
    set f : V → V := fun v => (hM v).choose
    have hadj : ∀ v, M.Adj v (f v) := fun v => (hM v).choose_spec.1
    have hinj : Function.Injective f := by
      intro a b hab
      have h1 : M.Adj (f a) a := (hadj a).symm
      have h2 : M.Adj (f a) b := hab ▸ (hadj b).symm
      exact ((hM (f a)).choose_spec.2 a h1).trans ((hM (f a)).choose_spec.2 b h2).symm
    have hsub : f '' s ⊆ ⋃ x ∈ s, G.neighborSet x := by
      rintro _ ⟨v, hv, rfl⟩
      exact Set.mem_biUnion hv (M.adj_sub (hadj v))
    have hfin : (⋃ x ∈ s, G.neighborSet x).Finite :=
      hs.biUnion fun x _ => Set.toFinite (G.neighborSet x)
    calc s.ncard = (f '' s).ncard := (Set.ncard_image_of_injective s hinj).symm
      _ ≤ (⋃ x ∈ s, G.neighborSet x).ncard := Set.ncard_le_ncard hsub hfin
  · simp [hs.ncard]

/-- **Hall's marriage theorem**: a locally finite bipartite graph has a perfect matching if and
only if Hall's condition holds, i.e. every set of vertices `s` satisfies
`s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard`.

The forward direction holds for any locally finite graph; the reverse direction is Mathlib's
`SimpleGraph.exists_isPerfectMatching_of_forall_ncard_le`. -/
theorem halls_marriage [G.LocallyFinite] {p₁ p₂ : Set V} (hG : G.IsBipartiteWith p₁ p₂) :
    (∃ M : G.Subgraph, M.IsPerfectMatching) ↔
      ∀ s : Set V, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard := by
  constructor
  · rintro ⟨M, hM⟩
    exact ncard_le_ncard_biUnion_neighborSet_of_isPerfectMatching hM
  · exact fun h => SimpleGraph.exists_isPerfectMatching_of_forall_ncard_le hG h

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

