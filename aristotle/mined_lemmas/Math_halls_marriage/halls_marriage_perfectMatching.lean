import Mathlib

/-!
# Halls Marriage
Category: Pure Mathematics
Target: Math.halls_marriage
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Function

namespace Math

/-- **Hall's Marriage Theorem** for a bipartite graph.

The bipartite graph is given by its adjacency relation `r : V → W → Prop` between the two
(finite) sides `V` and `W`.  A *matching saturating `V`* is an injective function `f : V → W`
with `v` adjacent to `f v` for every `v : V`.

Such a matching exists if and only if *Hall's condition* holds: every set `A` of vertices of
`V` has at least `#A` neighbours in `W`.

This is Mathlib's `Fintype.all_card_le_filter_rel_iff_exists_injective`. -/

theorem halls_marriage_perfectMatching {V W : Type*} [Fintype V] [Fintype W]
    (hcard : Fintype.card V = Fintype.card W) (r : V → W → Prop) [DecidableRel r] :
    (∃ M : (bipartiteGraph r).Subgraph, M.IsPerfectMatching) ↔
      ∀ A : Finset V, #A ≤ #{w | ∃ v ∈ A, r v w} := by
  constructor
  · rintro ⟨M, hM⟩
    exact (halls_marriage r).mpr (exists_injective_of_isPerfectMatching r hM)
  · intro h
    obtain ⟨f, hf, hr⟩ := (halls_marriage r).mp h
    exact exists_isPerfectMatching_of_injective hcard r hf hr

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

