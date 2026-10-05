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


theorem HLT_of_move {h h' : Hydra} (hm : Move h h') : HLT h' h := by
  induction hm with
  | chopHead l₁ l₂ =>
    refine (HLT_iff_cutExpand _ _).2 ⟨0, .node [], by simp, ?_⟩
    simp only [add_zero, ← Multiset.coe_add, ← Multiset.cons_coe, ← Multiset.singleton_add]
    abel
  | dup n l₁ l₂ r₁ r₂ =>
    refine (HLT_iff_cutExpand _ _).2
      ⟨Multiset.replicate n (.node (r₁ ++ r₂)), .node (r₁ ++ .node [] :: r₂), ?_, ?_⟩
    · intro a' ha'
      rw [Multiset.eq_of_mem_replicate ha']
      refine (HLT_iff_cutExpand _ _).2 ⟨0, .node [], by simp, ?_⟩
      simp only [add_zero, ← Multiset.coe_add, ← Multiset.cons_coe, ← Multiset.singleton_add]
      abel
    · simp only [← Multiset.coe_add, ← Multiset.cons_coe, ← Multiset.singleton_add,
        ← Multiset.coe_replicate]
      abel
  | deeper l₁ l₂ a b _ ih =>
    refine (HLT_iff_cutExpand _ _).2 ⟨{b}, a, ?_, ?_⟩
    · intro a' ha'
      rw [Multiset.mem_singleton.1 ha']
      exact ih
    · simp only [← Multiset.coe_add, ← Multiset.cons_coe, ← Multiset.singleton_add]
      abel

/-- The reversed move relation is well founded: the hydra always loses. -/
