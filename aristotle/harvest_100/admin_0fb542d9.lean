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
def toOrderHom : α →o α := ⟨W.broadcast, W.mono⟩

/-- A state is *stable* (an ignition fixpoint) when broadcasting it changes nothing. -/
def IsStable (x : α) : Prop := W.broadcast x = x

/-- The iteration of the broadcast operator from the empty workspace is monotone in the
number of broadcast cycles. -/
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
theorem global_workspace_fixpoint {α : Type*} [CompleteLattice α] [Finite α]
    (W : GlobalWorkspace α) :
    ∃ x : α, W.IsStable x ∧ ∀ y : α, W.IsStable y → x ≤ y :=
  ⟨OrderHom.lfp W.toOrderHom, OrderHom.map_lfp W.toOrderHom,
    fun _ hy => OrderHom.lfp_le W.toOrderHom hy.le⟩

/-- Packaged form of the target: the least fixed point of the broadcast operator is the
least element of the set of stable global-workspace states. -/
theorem global_workspace_isLeast_stable {α : Type*} [CompleteLattice α]
    (W : GlobalWorkspace α) :
    IsLeast {x : α | W.IsStable x} (OrderHom.lfp W.toOrderHom) :=
  ⟨OrderHom.map_lfp W.toOrderHom, fun _ hy => OrderHom.lfp_le W.toOrderHom hy.le⟩

/-- The least stable state of a global workspace is unique. -/
theorem global_workspace_fixpoint_unique {α : Type*} [CompleteLattice α]
    (W : GlobalWorkspace α) {x y : α}
    (hx : W.IsStable x) (hx' : ∀ z : α, W.IsStable z → x ≤ z)
    (hy : W.IsStable y) (hy' : ∀ z : α, W.IsStable z → y ≤ z) : x = y :=
  le_antisymm (hx' y hy) (hy' x hx)

/-- On a *finite* state lattice the least fixed point is actually *reached* by iterating the
broadcast operator finitely many times from the empty workspace `⊥`: some finite ignition
cascade `broadcast^[n] ⊥` is stable and lies below every stable state. -/
theorem global_workspace_fixpoint_iterate {α : Type*} [CompleteLattice α] [Finite α]
    (W : GlobalWorkspace α) :
    ∃ n : ℕ, W.IsStable (W.broadcast^[n] ⊥) ∧
      ∀ y : α, W.IsStable y → W.broadcast^[n] ⊥ ≤ y := by
  have hmono := W.monotone_iterate_bot
  obtain ⟨m, n, hmn, hEq⟩ :
      ∃ m n : ℕ, m ≠ n ∧ W.broadcast^[m] (⊥ : α) = W.broadcast^[n] ⊥ :=
    Finite.exists_ne_map_eq_of_infinite fun n : ℕ => W.broadcast^[n] (⊥ : α)
  -- Along the increasing chain, a repetition forces stabilisation at the earlier index.
  have key : ∀ i j : ℕ, i < j → W.broadcast^[i] (⊥ : α) = W.broadcast^[j] ⊥ →
      W.IsStable (W.broadcast^[i] (⊥ : α)) := by
    intro i j hij h
    have h1 : W.broadcast^[i] (⊥ : α) ≤ W.broadcast^[i + 1] ⊥ := hmono (Nat.le_succ i)
    have h2 : W.broadcast^[i + 1] (⊥ : α) ≤ W.broadcast^[j] ⊥ := hmono hij
    have h3 : W.broadcast^[i + 1] (⊥ : α) = W.broadcast^[i] ⊥ :=
      le_antisymm (by rw [h]; exact h2) h1
    have h4 : W.broadcast (W.broadcast^[i] (⊥ : α)) = W.broadcast^[i] ⊥ := by
      rw [← Function.iterate_succ_apply' W.broadcast i ⊥]; exact h3
    exact h4
  rcases lt_or_gt_of_ne hmn with h | h
  · exact ⟨m, key m n h hEq, fun y hy => W.iterate_bot_le_of_isStable hy m⟩
  · exact ⟨n, key n m h hEq.symm, fun y hy => W.iterate_bot_le_of_isStable hy n⟩

end Frontier

