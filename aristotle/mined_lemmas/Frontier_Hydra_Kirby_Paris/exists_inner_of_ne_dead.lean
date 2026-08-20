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

theorem exists_inner_of_ne_dead :
    ∀ x : Hydra, x ≠ node [] → ∀ a b : List Hydra, ∃ y, Inner (node (a ++ x :: b)) y := by
  refine ind_children ?_
  intro L ih hL a b
  cases L with
  | nil => exact absurd rfl hL
  | cons c cs =>
      by_cases hc : c = node []
      · subst hc
        exact ⟨_, by simpa using Inner.grand 0 a b [] cs⟩
      · obtain ⟨y, hy⟩ := ih c (by simp) hc [] cs
        exact ⟨_, Inner.deep a b hy⟩

/-- Conversely to `step_ne_dead`: a hydra which is not dead admits a move. -/
