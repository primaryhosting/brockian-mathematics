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

def IsWorkspaceFixpoint (B : Broadcast S) (s : S) : Prop := B.ignite s = s

/-- Every iterate of `ignite` started from the empty workspace `⊥` lies below any fixpoint. -/

theorem iterate_bot_le_fixpoint (B : Broadcast S) {t : S} (ht : IsWorkspaceFixpoint B t) :
    ∀ n : ℕ, B.ignite^[n] ⊥ ≤ t := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      calc B.ignite (B.ignite^[n] ⊥) ≤ B.ignite t := B.mono ih
        _ = t := ht

/-- On a *finite* state lattice the ascending chain `⊥ ≤ ignite ⊥ ≤ ignite² ⊥ ≤ ⋯`
stabilizes after finitely many broadcast rounds. -/
