import Mathlib
/-!
# Hydra Kirby Paris
Category: Frontier — Set Theory
Target: Frontier.Hydra_Kirby_Paris
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

set_option grind.warning false

namespace Frontier
namespace KirbyParis

/-!
## Hydras

A *hydra* is a finite rooted tree.  We encode it as an inductive type whose only
constructor takes the (ordered) list of subtrees hanging off the root; the order of the
list carries no meaning, and all statements below are invariant under permuting it.
-/

/-- A hydra: a finite rooted tree, given by the list of subtrees attached to its root. -/
inductive Hydra : Type
  | node : List Hydra → Hydra

namespace Hydra

/-- The dead hydra: a bare root with no heads. -/

theorem HR_child {s s' : Hydra} (h : HR s' s) (l₁ l₂ : List Hydra) :
    HR (.node (l₁ ++ s' :: l₂)) (.node (l₁ ++ s :: l₂)) := by
  refine HR.mk {s'} s ?_ ?_
  · intro a' ha'
    rw [Multiset.mem_singleton] at ha'
    exact ha' ▸ h
  · rw [coe_append_cons, coe_append_cons]
    abel

/-- Replacing one child `t` of the root by any number of copies of a strictly smaller
hydra `t'` strictly decreases the hydra. -/
