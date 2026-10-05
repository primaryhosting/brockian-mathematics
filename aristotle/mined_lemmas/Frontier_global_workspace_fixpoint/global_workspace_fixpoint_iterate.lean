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

