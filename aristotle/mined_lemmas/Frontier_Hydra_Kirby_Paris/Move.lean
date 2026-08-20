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

def Move (h h' : Hydra) : Prop := Chop h h' ∨ Deep h h'

/-!
## A well-founded relation on hydras

We compare hydras by the relation `HR`, a "one-step" version of the Cantor-normal-form
order: `HR h' h` holds when the multiset of subtrees of `h'` is obtained from that of `h`
by deleting one subtree `a` and inserting finitely many subtrees, each `HR`-smaller than
`a`.  This is exactly `Relation.CutExpand HR` applied to the multisets of children, so
Mathlib's `Acc.cutExpand` / `Relation.acc_of_singleton` (from `Mathlib/Logic/Hydra.lean`,
the *simple* hydra game) can be used to run the induction.
-/

/-- The one-step Cantor-normal-form ordering on hydras. -/
inductive HR : Hydra → Hydra → Prop
  | mk {ts' ts : List Hydra} (u : Multiset Hydra) (a : Hydra) :
      (∀ a' ∈ u, HR a' a) →
      ((ts' : Multiset Hydra) + {a} = (ts : Multiset Hydra) + u) →
      HR (.node ts') (.node ts)

