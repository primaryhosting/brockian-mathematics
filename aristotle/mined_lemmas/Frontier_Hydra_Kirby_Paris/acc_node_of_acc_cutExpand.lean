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

private theorem acc_node_of_acc_cutExpand {s : Multiset Hydra}
    (hs : Acc (Relation.CutExpand HR) s) :
    ∀ ts : List Hydra, (ts : Multiset Hydra) = s → Acc HR (.node ts) := by
  induction hs with
  | intro s _ ih =>
    intro ts hts
    refine Acc.intro _ ?_
    rintro y hy
    cases hy with
    | @mk ts' _ u a hu he =>
      exact ih _ (hts ▸ (⟨u, a, hu, he⟩ : Relation.CutExpand HR _ _)) ts' rfl

/-- The ordering `HR` on hydras is well-founded.  This is the combinatorial heart of the
Kirby–Paris theorem; it is deduced from Mathlib's `Relation.acc_of_singleton` and
`Acc.cutExpand`. -/
