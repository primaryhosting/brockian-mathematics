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

theorem exists_iterate_bot_stabilizes [Finite S] (B : Broadcast S) :
    ∃ n : ℕ, B.ignite^[n + 1] ⊥ = B.ignite^[n] ⊥ := by
  have hchain : Monotone (fun n : ℕ => B.ignite^[n] (⊥ : S)) :=
    B.mono.monotone_iterate_of_le_map bot_le
  obtain ⟨a, b, hab, hval⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => B.ignite^[n] (⊥ : S))
  rcases lt_or_gt_of_ne hab with h | h
  · refine ⟨a, le_antisymm ?_ (hchain (Nat.le_succ a))⟩
    calc B.ignite^[a + 1] (⊥ : S) ≤ B.ignite^[b] ⊥ := hchain h
      _ = B.ignite^[a] ⊥ := hval.symm
  · refine ⟨b, le_antisymm ?_ (hchain (Nat.le_succ b))⟩
    calc B.ignite^[b + 1] (⊥ : S) ≤ B.ignite^[a] ⊥ := hchain h
      _ = B.ignite^[b] ⊥ := hval

/-- **Global workspace fixpoint (Knaster–Tarski, finite state lattice).**

A monotone broadcast operator `B` on a finite complete lattice `S` of states has a
least fixed point: a state `s` that is stable under broadcasting (`B.ignite s = s`)
and below every other stable state.  Moreover it is *reached constructively* by
finitely many broadcast rounds from the empty workspace, `s = B.ignite^[n] ⊥`.

The existence part alone is `OrderHom.isLeast_lfp` in Mathlib (Knaster–Tarski for
complete lattices); finiteness additionally gives the terminating iteration. -/
