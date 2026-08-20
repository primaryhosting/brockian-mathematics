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

theorem Hydra.strong_induction {P : Hydra → Prop}
    (h : ∀ ts : List Hydra, (∀ t ∈ ts, P t) → P (Hydra.node ts)) : ∀ x, P x :=
  Hydra.rec (motive_1 := P) (motive_2 := fun ts => ∀ t ∈ ts, P t)
    (fun ts ih => h ts ih)
    (fun t ht => absurd ht List.not_mem_nil)
    (fun a l ha hl t ht => by
      rcases List.mem_cons.1 ht with rfl | ht
      · exact ha
      · exact hl t ht)

/-!
## The moves of the Kirby–Paris hydra game

Hercules chops off a *head*, i.e. a leaf of the tree.

* If the head grows directly out of the root, it is simply removed (`Chop`).
* Otherwise the head has a parent `t` and a grandparent.  The head is removed from `t`,
  producing `t'`, and then the grandparent grows some number `k` of copies of `t'` in place
  of `t`.  (The classical rule takes `k = n + 1` at stage `n`; we allow an *arbitrary*
  `k : ℕ`, which makes the termination theorem below strictly stronger.)

`Deep` describes the second kind of move, by recursion on the distance from the root.
-/

/-- `Chop h h'` : `h'` is obtained from `h` by cutting off a head that grows directly out of
the root of `h`. -/
inductive Chop : Hydra → Hydra → Prop
  | mk (l₁ l₂ : List Hydra) :
      Chop (.node (l₁ ++ .node [] :: l₂)) (.node (l₁ ++ l₂))

/-- `Deep h h'` : `h'` is obtained from `h` by cutting off a head at distance at least `2`
from the root, together with the Kirby–Paris duplication at the grandparent of that head. -/
inductive Deep : Hydra → Hydra → Prop
  /-- The cut head is at distance exactly `2`: it is chopped off the child `t`, turning `t`
  into `t'`, and the root (the grandparent) then carries `k` copies of `t'` instead of `t`. -/
  | dup (l₁ l₂ : List Hydra) (t t' : Hydra) (k : ℕ) (h : Chop t t') :
      Deep (.node (l₁ ++ t :: l₂)) (.node (l₁ ++ List.replicate k t' ++ l₂))
  /-- The cut head is at distance at least `3`: the whole move takes place inside a single
  child `t` of the root. -/
  | nest (l₁ l₂ : List Hydra) (t t' : Hydra) (h : Deep t t') :
      Deep (.node (l₁ ++ t :: l₂)) (.node (l₁ ++ t' :: l₂))

/-- `Move h h'` : `h'` results from `h` by one legal move of the Kirby–Paris hydra game. -/
