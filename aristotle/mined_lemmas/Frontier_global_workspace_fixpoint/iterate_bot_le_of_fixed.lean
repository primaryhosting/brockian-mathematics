/-
# Global Workspace Fixpoint
Category: Frontier Mind
Target: Frontier.global_workspace_fixpoint
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-- A *global workspace* on a finite state lattice `α`: a broadcast operator
`broadcast : α → α` which is monotone (broadcasting from a larger workspace
content yields a larger workspace content). -/
structure GlobalWorkspace (α : Type*) [Lattice α] [OrderBot α] [Finite α] where
  /-- The broadcast (global-workspace) operator. -/
  broadcast : α → α
  /-- Broadcasting is monotone. -/
  mono : Monotone broadcast

/-- `m` is a least fixed point of `f`: it is a fixed point, and it is below
every fixed point of `f`. -/

theorem iterate_bot_le_of_fixed (hf : Monotone f) {x : α} (hx : f x = x) (n : ℕ) :
    f^[n] ⊥ ≤ x := by
  induction n with
  | zero => simp
  | succ n ih =>
      have : f (f^[n] ⊥) ≤ f x := hf ih
      rw [hx] at this
      simpa [Function.iterate_succ_apply'] using this

end Iteration

/--
**Knaster–Tarski for a global workspace.**

A monotone broadcast (global-workspace) operator on a finite state lattice has a
least fixed point, and this least fixed point is *reached* by finitely many
broadcast steps starting from the empty workspace `⊥`.
-/
