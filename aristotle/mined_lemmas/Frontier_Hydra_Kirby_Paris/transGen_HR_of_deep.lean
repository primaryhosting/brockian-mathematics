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

theorem transGen_HR_of_deep {t t' : Hydra} (h : Deep t t') :
    Relation.TransGen HR t' t := by
  induction h with
  | dup l₁ l₂ t t' k hc =>
    exact Relation.TransGen.single (HR_dup (HR_of_chop hc) l₁ l₂ k)
  | nest l₁ l₂ t t' _ ih =>
    exact Relation.TransGen.lift (fun s => Hydra.node (l₁ ++ s :: l₂))
      (fun _ _ hab => HR_child hab l₁ l₂) ih

/-- Every legal move of the Kirby–Paris hydra game strictly decreases the hydra with
respect to the well-founded relation `HR`. -/
