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

theorem stage_le_succ (n : ℕ) : W.stage n ≤ W.stage (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [stage_succ, stage_succ]
      exact W.mono ih

/-- The broadcast cascade is a monotone chain. -/
