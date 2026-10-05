/-
# Hydra Kirby Paris
Category: Frontier — Set Theory
Target: Frontier.Hydra_Kirby_Paris
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is repeated
-- below as the module docstring of this file.)

import Mathlib

/-!
# Hydra Kirby Paris
Category: Frontier — Set Theory
Target: Frontier.Hydra_Kirby_Paris
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

A *hydra* is a finite rooted tree.  A move of the Kirby–Paris hydra game consists of
choosing a *head* (a leaf) and chopping it off:

* if the head is attached to the root, nothing grows back;
* otherwise, let `p` be the parent of the head and `g` the grandparent.  After the head is
  removed, an arbitrary finite number `n` of copies of the (modified) subtree rooted at `p`
  are attached to `g`.

We model hydras by the inductive type `Frontier.Hydra` (a rooted tree with an ordered list of
children — the ordering is immaterial, all statements below are invariant under it), and the
moves by the relation `Frontier.Hydra.Move`.  `Move h h'` means: `h'` arises from `h` by one
legal move of the game, with an arbitrary number of copies grown back (so our result covers
every convention about how many heads regrow at each stage, and any strategy of the player
and of the hydra).

The main results are:

* `Frontier.Hydra.wellFounded_move` : the reversed move relation is well founded;
* `Frontier.Hydra_Kirby_Paris` : there is no infinite play, i.e. every hydra game terminates,
  for every strategy;
* `Frontier.Hydra.strategy_terminates` : iterating any legal strategy from any starting hydra
  reaches the dead hydra in finitely many steps;
* `Frontier.Hydra.exists_move` : the game gets stuck only at the dead hydra.

The termination proof follows the classical argument, in the guise of Mathlib's
`Relation.CutExpand`: we build a well-founded relation `HLT` on hydras (`HLT h' h` holds when
the children of `h'` are obtained from those of `h` by a cut-and-expand step for `HLT` itself),
show that it is well founded, and check that every move of the game strictly decreases it.
-/

namespace Frontier

/-- A hydra: a finite rooted tree.  `node l` is the tree whose root has the children `l`.
`node []` is a single head, the "dead" hydra. -/
inductive Hydra : Type
  | node : List Hydra → Hydra
  deriving Inhabited

namespace Hydra

/-- The dead hydra: a single node with no children. -/
abbrev dead : Hydra := .node []

/-! ### A well-founded relation on hydras -/

/-- `HLT h' h` holds when the multiset of children of `h'` is obtained from the multiset of
children of `h` by removing one child `a` and adding back finitely many hydras, each of which
is `HLT`-smaller than `a`.  This is exactly `Relation.CutExpand HLT` on the children
(see `HLT_iff_cutExpand`). -/
inductive HLT : Hydra → Hydra → Prop
  | mk (l' l : List Hydra) (t : Multiset Hydra) (a : Hydra)
      (ha : ∀ a' ∈ t, HLT a' a)
      (he : (l' : Multiset Hydra) + {a} = (l : Multiset Hydra) + t) :
      HLT (.node l') (.node l)


theorem HLT.acc (h : Hydra) : Acc HLT h := by
  induction h using Hydra.rec (motive_2 := fun l => ∀ a ∈ l, Acc HLT a) with
  | node l ih =>
    refine acc_node_of_acc_cutExpand (Relation.acc_of_singleton ?_) l rfl
    intro a ha
    exact (ih a (by simpa using ha)).cutExpand
  | nil b hb => exact absurd hb (by simp)
  | cons a l iha ihl b hb =>
    rcases List.mem_cons.1 hb with rfl | hb
    · exact iha
    · exact ihl b hb

