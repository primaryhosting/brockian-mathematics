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

theorem HR_irrefl : ∀ x y : Hydra, HR x y → x ≠ y := by
  intro x y h
  induction h with
  | @mk ts' ts u a hu he ih =>
    intro hxy
    have hts : ts' = ts := by injection hxy
    subst hts
    have hu' : ({a} : Multiset Hydra) = u := add_left_cancel he
    exact ih a (hu' ▸ Multiset.mem_singleton_self a) rfl

instance : Std.Irrefl HR := ⟨fun a h => HR_irrefl a a h rfl⟩

