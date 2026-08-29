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

theorem global_workspace_fixpoint_unique {α : Type*} [CompleteLattice α]
    (W : GlobalWorkspace α) {x y : α}
    (hx : W.IsStable x) (hx' : ∀ z : α, W.IsStable z → x ≤ z)
    (hy : W.IsStable y) (hy' : ∀ z : α, W.IsStable z → y ≤ z) : x = y :=
  le_antisymm (hx' y hy) (hy' x hx)

/-- On a *finite* state lattice the least fixed point is actually *reached* by iterating the
broadcast operator finitely many times from the empty workspace `⊥`: some finite ignition
cascade `broadcast^[n] ⊥` is stable and lies below every stable state. -/
