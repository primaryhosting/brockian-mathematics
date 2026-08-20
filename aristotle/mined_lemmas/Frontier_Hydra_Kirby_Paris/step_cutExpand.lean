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

theorem step_cutExpand {L L' : List Hydra} (hacc : ∀ c ∈ L, Acc Below c)
    (h : Step (node L) (node L')) :
    Relation.CutExpand BelowAcc (L' : Multiset Hydra) (L : Multiset Hydra) := by
  cases h with
  | top a b =>
      refine ⟨0, node [], by simp, ?_⟩
      rw [coe_append_cons]
      abel
  | inner h =>
      cases h with
      | grand k a b ca cb =>
          refine ⟨Multiset.replicate k (node (ca ++ cb)), node (ca ++ node [] :: cb), ?_, ?_⟩
          · intro y hy
            rw [Multiset.eq_of_mem_replicate hy]
            exact ⟨Step.top ca cb, Acc.inv (hacc _ (by simp)) (Step.top ca cb)⟩
          · rw [coe_append_cons]
            simp only [← Multiset.coe_add, Multiset.coe_replicate]
            abel
      | @deep a b c c' hcc' =>
          refine ⟨{c'}, c, ?_, ?_⟩
          · intro y hy
            rw [Multiset.mem_singleton.1 hy]
            exact ⟨Step.inner hcc', Acc.inv (hacc _ (by simp)) (Step.inner hcc')⟩
          · rw [coe_append_cons, coe_append_cons]
            abel

/-- Transfer of accessibility from the multiset of children to the hydra itself. -/
