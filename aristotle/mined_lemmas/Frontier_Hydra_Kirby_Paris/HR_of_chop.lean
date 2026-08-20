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

theorem HR_of_chop {t t' : Hydra} (h : Chop t t') : HR t' t := by
  cases h with
  | mk l₁ l₂ =>
    refine HR.mk 0 (.node []) (by simp) ?_
    rw [coe_append_cons]
    show ((l₁ : Multiset Hydra) + l₂) + {Hydra.node []}
      = ((l₁ : Multiset Hydra) + {Hydra.node []} + l₂) + 0
    abel

/-- `HR` is compatible with replacing one child of the root. -/
