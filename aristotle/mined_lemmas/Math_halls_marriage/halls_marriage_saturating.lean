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

