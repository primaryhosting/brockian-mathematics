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

/-- A global-workspace state `a` is *stable* under the broadcast operator `f`
when broadcasting does not change it, i.e. `a` is a fixed point of `f`. -/
def IsStable {α : Type*} (f : α → α) (a : α) : Prop := f a = a

/-- `a` is the *least stable state* (least fixed point) of the broadcast operator `f`:
it is stable, and it lies below every stable state. -/
def IsLeastStable {α : Type*} [Preorder α] (f : α → α) (a : α) : Prop :=
  IsStable f a ∧ ∀ b : α, IsStable f b → a ≤ b

/-- **Knaster–Tarski for a global workspace.**

On a finite state lattice `α` (a finite complete lattice, ordered by "amount of
information broadcast"), every monotone broadcast operator `f : α → α` has a least
fixed point: a state `a` with `f a = a` that is below every other fixed point.

The finiteness hypothesis `[Fintype α]` is included because the statement is phrased
for a *finite* state lattice; it is not needed for the proof, since the Knaster–Tarski
theorem holds on any complete lattice.

Proof: the least fixed point is `OrderHom.lfp ⟨f, hf⟩`; the two required facts are
Mathlib's `OrderHom.map_lfp` and `OrderHom.lfp_le`. -/
theorem global_workspace_fixpoint {α : Type*} [Fintype α] [CompleteLattice α]
    (f : α → α) (hf : Monotone f) :
    ∃ a : α, IsLeastStable f a := by
  refine ⟨OrderHom.lfp ⟨f, hf⟩, OrderHom.map_lfp ⟨f, hf⟩, ?_⟩
  intro b hb
  exact OrderHom.lfp_le _ hb.le

/-- Uniqueness: the least stable state of a broadcast operator is unique. -/
theorem isLeastStable_unique {α : Type*} [PartialOrder α] (f : α → α) {a b : α}
    (ha : IsLeastStable f a) (hb : IsLeastStable f b) : a = b :=
  le_antisymm (ha.2 b hb.1) (hb.2 a ha.1)

end Frontier

