/-
/-!
# Hydra Kirby Paris
Category: Frontier — Set Theory
Target: Frontier.Hydra_Kirby_Paris
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

set_option grind.warning false

namespace Frontier

/-- A *hydra* is a finite rooted tree: a node together with the (finite) list of the
hydras hanging from it.  Only the multiset of children matters for the game, but a list
representation is used so that the type is a genuine inductive type. -/
inductive Hydra : Type
  | node : List Hydra → Hydra

namespace Hydra

/-- Structural induction principle for hydras: to prove a property of every hydra it
suffices to prove it for `node L` assuming it for every element of `L`. -/

theorem exists_step_of_ne_dead (x : Hydra) (hx : x ≠ node []) : ∃ y, Step x y := by
  cases x with
  | node L =>
      cases L with
      | nil => exact absurd rfl hx
      | cons c cs =>
          by_cases hc : c = node []
          · subst hc
            exact ⟨node cs, by simpa using Step.top [] cs⟩
          · obtain ⟨y, hy⟩ := exists_inner_of_ne_dead c hc [] cs
            exact ⟨y, Step.inner (by simpa using hy)⟩

/-- One Kirby–Paris move on `node L` turns the multiset of children `L` into a multiset
obtained by removing one child and adding back finitely many strictly smaller ones:
this is a `CutExpand` step for the move relation. -/
