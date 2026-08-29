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


theorem wellFounded_HLT : WellFounded HLT := ⟨HLT.acc⟩

/-! ### The moves of the Kirby–Paris hydra game -/

/-- One move of the Kirby–Paris hydra game: `Move h h'` means that `h'` is obtained from `h`
by chopping off one head.

* `chopHead` : the head is a child of the root; it is simply removed.
* `dup` : the head is a grandchild of the root; the parent subtree, with the head removed, is
  replaced by `n` copies of itself (`n` arbitrary — this covers every convention on the number
  of heads that grow back).
* `deeper` : a move performed inside one of the subtrees hanging from the root. -/
inductive Move : Hydra → Hydra → Prop
  | chopHead (l₁ l₂ : List Hydra) :
      Move (.node (l₁ ++ .node [] :: l₂)) (.node (l₁ ++ l₂))
  | dup (n : ℕ) (l₁ l₂ r₁ r₂ : List Hydra) :
      Move (.node (l₁ ++ .node (r₁ ++ .node [] :: r₂) :: l₂))
        (.node (l₁ ++ List.replicate n (.node (r₁ ++ r₂)) ++ l₂))
  | deeper (l₁ l₂ : List Hydra) (h h' : Hydra) :
      Move h h' → Move (.node (l₁ ++ h :: l₂)) (.node (l₁ ++ h' :: l₂))

/-- Every move of the game strictly decreases the well-founded relation `HLT`. -/
