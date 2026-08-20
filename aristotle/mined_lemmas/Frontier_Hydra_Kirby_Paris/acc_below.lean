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

theorem acc_below : ∀ x : Hydra, Acc Below x := by
  refine ind_children ?_
  intro L ih
  have hsing : ∀ c ∈ (L : Multiset Hydra), Acc (Relation.CutExpand BelowAcc) {c} := by
    intro c hc
    exact Acc.cutExpand (belowAcc_sub.accessible (ih c (by simpa using hc)))
  exact acc_of_acc_children (Relation.acc_of_singleton hsing) L rfl (fun c hc => ih c hc)

/-- **Kirby–Paris, well-foundedness form.** The relation "is obtained by one hydra move"
is well founded; equivalently, there is no infinite play. -/
