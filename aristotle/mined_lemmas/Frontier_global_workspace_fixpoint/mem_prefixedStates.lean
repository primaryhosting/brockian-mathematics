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

/-- A **global workspace** on a state space `α`: a broadcast operator
`broadcast : α → α` that maps a global state to the state obtained after one round of
workspace broadcasting, assumed monotone (adding information to the workspace never
removes information from the result). -/
structure GlobalWorkspace (α : Type*) [Lattice α] where
  /-- The broadcast (global-workspace) operator. -/
  broadcast : α → α
  /-- Broadcasting is monotone. -/
  broadcast_mono : Monotone broadcast

variable {α : Type*} [Lattice α] [OrderTop α] [Fintype α]

/-- The set of *pre-fixed* (broadcast-stable) states of a global workspace:
states that the broadcast operator does not enlarge. -/

lemma mem_prefixedStates {W : GlobalWorkspace α} {a : α} :
    a ∈ prefixedStates W ↔ W.broadcast a ≤ a := by
  simp [prefixedStates]

/-- `gwLfp W` is below every pre-fixed state. -/
