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

theorem HR_dup {t t' : Hydra} (h : HR t' t) (l₁ l₂ : List Hydra) (k : ℕ) :
    HR (.node (l₁ ++ List.replicate k t' ++ l₂)) (.node (l₁ ++ t :: l₂)) := by
  refine HR.mk (Multiset.replicate k t') t ?_ ?_
  · intro a' ha'
    exact (Multiset.eq_of_mem_replicate ha') ▸ h
  · rw [coe_append_append, coe_append_cons, coe_replicate]
    abel

/-- Every deep move (cut at distance ≥ 2, with duplication) strictly decreases the hydra,
in the transitive closure of `HR`. -/
