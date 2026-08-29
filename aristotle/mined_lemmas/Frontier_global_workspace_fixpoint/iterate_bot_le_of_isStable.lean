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

theorem iterate_bot_le_of_isStable {y : α} (hy : W.IsStable y) (n : ℕ) :
    W.broadcast^[n] (⊥ : α) ≤ y := by
  induction n with
  | zero => simp
  | succ k ih =>
      calc W.broadcast^[k + 1] (⊥ : α) = W.broadcast (W.broadcast^[k] ⊥) :=
            Function.iterate_succ_apply' _ _ _
        _ ≤ W.broadcast y := W.mono ih
        _ = y := hy

end GlobalWorkspace

/-- **Global workspace fixpoint (Knaster–Tarski).**
A monotone broadcast operator on a finite state lattice reaches a least fixed point:
there is a stable global-workspace state that lies below every stable state.

The core of the proof is Mathlib's Knaster–Tarski theory of least fixed points
(`OrderHom.map_lfp` and `OrderHom.lfp_le`); finiteness of the state space is not needed
for this form of the statement. -/
