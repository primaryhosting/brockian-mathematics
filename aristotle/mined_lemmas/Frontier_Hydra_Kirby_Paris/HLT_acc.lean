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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Hydra Kirby Paris
Category: Frontier — Set Theory
Target: Frontier.Hydra_Kirby_Paris
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is repeated as a module docstring after the imports; Lean does not
-- allow a `/-!` doc comment to precede the `import` commands.)

import Mathlib

/-!
# Hydra Kirby Paris
Category: Frontier — Set Theory
Target: Frontier.Hydra_Kirby_Paris
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The Kirby–Paris hydra theorem

A *hydra* is a finite rooted tree, modelled here by the nested inductive type `Hydra`
(a node carries the list of its children; the intended semantics is that the order of the
children is irrelevant, so all statements below are phrased in terms of the *multiset* of
children).

Hercules fights the hydra by chopping off a *head*, i.e. a leaf of the tree at distance at
least one from the root.

* If the head is a child of the root it is simply removed (`Hydra.Chop`).
* Otherwise, let `c` be the parent of the head, and let `c'` be `c` with the head removed.
  The hydra grows back: `c` is replaced, among the children of its own parent (the
  grandparent of the head), by `n + 1` copies of `c'`, where `n` is arbitrary and may depend
  on the stage of the game (`Hydra.Deep.grand`, propagated upwards by `Hydra.Deep.inner`).

`Hydra.Move n` is the union of these two kinds of moves.  The theorem of Kirby and Paris
states that Hercules always wins, no matter which heads he chops and no matter how fast the
hydra grows.  This is `Frontier.Hydra_Kirby_Paris` below: for every sequence of hydras in
which each hydra is obtained from the previous one by a legal move as long as the hydra is
still alive, the dead hydra `Hydra.dead` (a single root with no children) is reached after
finitely many steps.

(The Kirby–Paris theorem is famously *not* provable in Peano arithmetic; that
independence result is a statement about PA and is not formalized here.  The proof given
below is the usual one, carried out in the ambient set theory of Lean/Mathlib: hydras are
ordered by the "nested multiset" ordering `Hydra.HLT`, whose well-foundedness is obtained
from the well-foundedness of `Relation.CutExpand` — the multiset hydra game of
`Mathlib/Logic/Hydra.lean` — by induction on the tree, and every legal move strictly
decreases a hydra in this ordering.)
-/

namespace Frontier

/-- A hydra: a finite rooted tree, given by the list of the subtrees hanging at the root.
The order of the children is irrelevant, and all notions below only depend on the
*multiset* of children. -/
inductive Hydra where
  | node : List Hydra → Hydra

namespace Hydra

/-- The dead hydra: a root with no children. -/

theorem HLT_acc (h : Hydra) : Acc HLT h :=
  Hydra.rec (motive_1 := fun h => Acc HLT h) (motive_2 := fun l => ∀ x ∈ l, Acc HLT x)
    (fun l ih => acc_node_of_acc_children
      (Relation.acc_of_singleton (fun a ha => Acc.cutExpand (ih a (by simpa using ha)))) l rfl)
    (fun x hx => absurd hx (List.not_mem_nil))
    (fun _ _ ihh iht x hx => by
      rcases List.mem_cons.1 hx with rfl | h
      · exact ihh
      · exact iht x h)
    h

/-- The nested multiset ordering on hydras is well-founded. -/
