/-!
# Global Workspace Fixpoint
Category: Frontier Mind
Target: Frontier.global_workspace_fixpoint
Statement: A monotone broadcast (global-workspace) operator on a finite state lattice reaches a least fixed point (Knaster–Tarski).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
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
theorem global_workspace_fixpoint_eq_lfp [Finite S] (B : Broadcast S) {s : S}
    (hs : IsWorkspaceFixpoint B s) (hmin : ∀ t : S, IsWorkspaceFixpoint B t → s ≤ t) :
    s = OrderHom.lfp ⟨B.ignite, B.mono⟩ := by
  obtain ⟨hfix, hle⟩ := OrderHom.isLeast_lfp (⟨B.ignite, B.mono⟩ : S →o S)
  exact le_antisymm (hmin _ hfix) (hle hs)

end Frontier

