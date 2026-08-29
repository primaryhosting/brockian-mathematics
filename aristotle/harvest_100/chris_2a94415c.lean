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
noncomputable def prefixedStates (W : GlobalWorkspace α) : Finset α :=
  {a : α | W.broadcast a ≤ a}

/-- The candidate least fixed point of a global workspace on a finite lattice:
the meet of all pre-fixed states. -/
noncomputable def gwLfp (W : GlobalWorkspace α) : α :=
  (prefixedStates W).inf id

omit [OrderTop α] in
lemma mem_prefixedStates {W : GlobalWorkspace α} {a : α} :
    a ∈ prefixedStates W ↔ W.broadcast a ≤ a := by
  simp [prefixedStates]

/-- `gwLfp W` is below every pre-fixed state. -/
lemma gwLfp_le_of_prefixed {W : GlobalWorkspace α} {a : α} (ha : W.broadcast a ≤ a) :
    gwLfp W ≤ a :=
  Finset.inf_le (f := id) (mem_prefixedStates.mpr ha)

/-- `gwLfp W` is itself pre-fixed. -/
lemma broadcast_gwLfp_le (W : GlobalWorkspace α) :
    W.broadcast (gwLfp W) ≤ gwLfp W := by
  refine Finset.le_inf ?_
  intro a ha
  have ha' : W.broadcast a ≤ a := mem_prefixedStates.mp ha
  exact le_trans (W.broadcast_mono (gwLfp_le_of_prefixed ha')) ha'

/-- `gwLfp W` is a fixed point of the broadcast operator. -/
lemma broadcast_gwLfp (W : GlobalWorkspace α) :
    W.broadcast (gwLfp W) = gwLfp W := by
  refine le_antisymm (broadcast_gwLfp_le W) ?_
  exact gwLfp_le_of_prefixed (W.broadcast_mono (broadcast_gwLfp_le W))

/-- **Global workspace fixpoint theorem** (Knaster–Tarski, finite case).

A monotone broadcast (global-workspace) operator on a finite state lattice has a least
fixed point, namely the meet `gwLfp W` of all its pre-fixed states: it is a fixed point,
and it is below every fixed point. -/
theorem global_workspace_fixpoint (W : GlobalWorkspace α) :
    IsLeast {a : α | W.broadcast a = a} (gwLfp W) :=
  ⟨broadcast_gwLfp W, fun _ hb => gwLfp_le_of_prefixed (le_of_eq hb)⟩

/-- Existence form: some state is a least fixed point of the broadcast operator. -/
theorem exists_least_broadcast_fixpoint (W : GlobalWorkspace α) :
    ∃ a : α, W.broadcast a = a ∧ ∀ b : α, W.broadcast b = b → a ≤ b :=
  ⟨gwLfp W, (global_workspace_fixpoint W).1, fun _ hb => (global_workspace_fixpoint W).2 hb⟩

end Frontier

