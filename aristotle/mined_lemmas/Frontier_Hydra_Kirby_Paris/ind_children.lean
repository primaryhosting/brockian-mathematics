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

theorem ind_children {motive : Hydra → Prop}
    (H : ∀ L : List Hydra, (∀ c ∈ L, motive c) → motive (node L)) (x : Hydra) : motive x :=
  Hydra.rec (motive_1 := motive) (motive_2 := fun L => ∀ c ∈ L, motive c)
    (fun L ih => H L ih)
    (by simp)
    (fun t ts iht ihts c hc => by
      rcases List.mem_cons.1 hc with rfl | hc
      · exact iht
      · exact ihts c hc)
    x

/-- Auxiliary multiset computation: as a multiset, `a ++ x :: b` is `{x}` plus `a ++ b`. -/
