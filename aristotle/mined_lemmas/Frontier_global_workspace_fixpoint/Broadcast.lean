/-
# Global Workspace Fixpoint
Category: Frontier Mind
Target: Frontier.global_workspace_fixpoint
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment because Lean requires `import` to be the
-- first command in a file; the same text is repeated as a module docstring below.)

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

/-- A *global workspace* (broadcast) system on a state lattice `α`: a monotone operator
`op` that takes the current global state to the state after one round of broadcast. -/
structure Broadcast (α : Type*) [Lattice α] where
  /-- The broadcast operator. -/
  op : α → α
  /-- Broadcasting is monotone: more information in, more information out. -/
  mono : Monotone op

variable {α : Type*} [Lattice α] [OrderBot α]

/-- The `n`-th broadcast round starting from the empty workspace `⊥`. -/

lemma Broadcast.iter_le_of_op_le (W : Broadcast α) {b : α} (hb : W.op b ≤ b) (n : ℕ) :
    W.iter n ≤ b := by
  induction n with
  | zero => simp
  | succ k ih => exact (W.iter_succ k ▸ (W.mono ih).trans hb)

/-- **Knaster–Tarski for a finite global workspace.**
A monotone broadcast operator on a finite state lattice reaches a least fixed point:
there is a state `a` that is invariant under broadcasting, is below every pre-fixed point
(in particular below every fixed point), and is attained after finitely many broadcast
rounds started from the empty workspace `⊥`. -/
