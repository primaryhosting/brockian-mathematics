import Mathlib
/-!
# Global Workspace Fixpoint
Category: Frontier Mind
Target: Frontier.global_workspace_fixpoint
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

namespace Frontier

/-- The set of *global-workspace states* that are fixed by a broadcast operator `f`:
states in which one further round of broadcasting changes nothing. -/

lemma broadcastIter_monotone {α : Type*} [CompleteLattice α] (f : α →o α) :
    Monotone (broadcastIter f) :=
  f.monotone.monotone_iterate_of_le_map bot_le

/-- Every broadcast round stays below any fixed point of the broadcast operator. -/
