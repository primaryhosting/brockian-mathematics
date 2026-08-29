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

/-- A *global workspace* on a state lattice `α`: a broadcast (ignition) operator sending the
currently active contents to the contents that become active after one broadcast cycle.
The operator is monotone: activating more contents can only lead to more contents being
broadcast. -/
structure GlobalWorkspace (α : Type*) [CompleteLattice α] where
  /-- The broadcast (ignition) step of the global workspace. -/
  broadcast : α → α
  /-- Broadcasting is monotone in the current workspace content. -/
  mono : Monotone broadcast

namespace GlobalWorkspace

variable {α : Type*} [CompleteLattice α] (W : GlobalWorkspace α)

/-- The broadcast operator packaged as a bundled order homomorphism. -/

theorem monotone_iterate_bot : Monotone fun n : ℕ => W.broadcast^[n] (⊥ : α) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
      have := W.mono ih
      simpa [Function.iterate_succ_apply'] using this

/-- Every finite ignition cascade started from the empty workspace stays below any stable
state. -/
