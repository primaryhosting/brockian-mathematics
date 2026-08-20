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

/-- A **broadcast (global-workspace) operator** on a state lattice `S`:
a map `ignite : S → S` sending a coalition of active contents to the contents that
become globally available after one broadcast step, required to be `Monotone`
(more active content in, no less active content out). -/
structure Broadcast (S : Type*) [CompleteLattice S] where
  /-- One global broadcast step. -/
  ignite : S → S
  /-- Broadcasting is monotone in the current workspace content. -/
  mono : Monotone ignite

variable {S : Type*} [CompleteLattice S]

/-- A state is a *workspace fixpoint* when broadcasting it changes nothing:
the global workspace is stable / self-sustaining. -/

theorem global_workspace_fixpoint [Finite S] (B : Broadcast S) :
    ∃ s : S, IsWorkspaceFixpoint B s ∧
      (∀ t : S, IsWorkspaceFixpoint B t → s ≤ t) ∧
      ∃ n : ℕ, s = B.ignite^[n] ⊥ := by
  obtain ⟨n, hn⟩ := exists_iterate_bot_stabilizes B
  refine ⟨B.ignite^[n] ⊥, ?_, ?_, ⟨n, rfl⟩⟩
  · have : B.ignite (B.ignite^[n] (⊥ : S)) = B.ignite^[n + 1] ⊥ :=
      (Function.iterate_succ_apply' B.ignite n ⊥).symm
    exact this.trans hn
  · intro t ht
    exact iterate_bot_le_fixpoint B ht n

/-- The state produced by `global_workspace_fixpoint` is exactly the Knaster–Tarski
least fixed point `OrderHom.lfp` of the broadcast operator. -/
