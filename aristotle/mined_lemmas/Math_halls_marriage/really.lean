import Mathlib
/-!
# Halls Marriage
Category: Pure Mathematics
Target: Math.halls_marriage
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
A self-contained development of Hall's marriage theorem.

* `Math.hall_exists_injective_iff` : the combinatorial ("system of distinct representatives")
  form, proved from scratch by induction (it does *not* use Mathlib's Hall theorem).
* `Math.halls_marriage` : a bipartite graph has a perfect matching iff Hall's condition holds.
-/

namespace Math

open Finset

section Core

variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

omit [DecidableEq ι] in

theorem really produces matchings: the single-edge graph on `Bool` is bipartite with parts
`{false}`, `{true}`, satisfies Hall's condition, and hence has a perfect matching. -/
example : ∃ M : (⊤ : SimpleGraph Bool).Subgraph, M.IsPerfectMatching := by
  have hb : (⊤ : SimpleGraph Bool).IsBipartiteWith {false} {true} := by
    constructor
    · simp
    · rintro v w h; cases v <;> cases w <;> simp_all
  refine (halls_marriage hb).mpr fun s => ?_
  have h : (⋃ v ∈ s, (⊤ : SimpleGraph Bool).neighborSet v) = (fun b => !b) '' s := by
    ext y
    simp only [Set.mem_iUnion, SimpleGraph.mem_neighborSet, top_adj, Set.mem_image, exists_prop]
    constructor
    · rintro ⟨v, hv, hne⟩; exact ⟨v, hv, by cases v <;> cases y <;> simp_all⟩
    · rintro ⟨v, hv, rfl⟩; exact ⟨v, hv, by cases v <;> simp⟩
  rw [h, Set.ncard_image_of_injective _ (fun a b => by cases a <;> cases b <;> simp)]

end Graph

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

