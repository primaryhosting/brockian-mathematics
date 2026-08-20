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

/-!
# Knaster–Tarski for a global workspace (broadcast) operator

A *global workspace* over a finite state lattice `α` consists of a `broadcast`
operator `α → α` which is monotone: enriching the current workspace content can
only enrich what gets broadcast.

The main theorem `Frontier.global_workspace_fixpoint` states that such an
operator has a least fixed point, which is moreover reached by iterating the
operator finitely many times (at most `Fintype.card α` times) starting from the
empty workspace `⊥`.
-/

namespace Frontier

variable {α : Type*}

/-- A **global workspace** on a state lattice `α`: a monotone broadcast operator. -/
structure GlobalWorkspace (α : Type*) [Lattice α] [BoundedOrder α] where
  /-- The broadcast operator: given the current workspace state, the new state. -/
  broadcast : α → α
  /-- Broadcasting is monotone in the workspace content. -/
  mono : Monotone broadcast

section

namespace GlobalWorkspace

variable [Lattice α] [BoundedOrder α] (W : GlobalWorkspace α)

/-- The `n`-th stage of the broadcast cascade, started from the empty workspace `⊥`. -/

theorem exists_least_fixpoint_of_broadcast :
    ∃ x : α, W.broadcast x = x ∧ (∀ y : α, W.broadcast y ≤ y → x ≤ y) ∧
      ∃ n ≤ Fintype.card α, W.broadcast^[n] ⊥ = x := by
  obtain ⟨n, hn, hstab⟩ := W.exists_stage_stabilises
  refine ⟨W.stage n, W.broadcast_fixed_of_stage_succ_eq hstab, ?_, ⟨n, hn, rfl⟩⟩
  intro y hy
  exact W.stage_le_of_prefixed hy n

end GlobalWorkspace

/--
**Knaster–Tarski for a global workspace.**

A monotone broadcast (global-workspace) operator `W.broadcast` on a finite state
lattice `α` reaches a least fixed point: there is a state `x` with
`W.broadcast x = x` which lies below every prefixed point `y`
(i.e. `W.broadcast y ≤ y`), and in particular below every fixed point.
Moreover this least fixed point is reached in finitely many broadcast rounds:
`x = W.broadcast^[n] ⊥` for some `n ≤ Fintype.card α`, starting from the empty
workspace `⊥`.
-/
