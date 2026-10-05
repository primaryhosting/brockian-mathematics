/-
# Hydra Kirby Paris
Category: Frontier — Set Theory
Target: Frontier.Hydra_Kirby_Paris
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to be the first command of a file, so the header above is a plain
-- block comment rather than a `/-!` module docstring; its text is otherwise verbatim.)

import Mathlib

/-!
# Hydra Kirby Paris
Category: Frontier — Set Theory
Target: Frontier.Hydra_Kirby_Paris
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Overview

We formalise Kirby–Paris hydras and the statement that *every* hydra game terminates, no matter
which head Hercules chops and no matter how fast the hydra grows new heads.

* A hydra is a finite rooted tree, `Hydra.node : List Hydra → Hydra` (the list of subtrees is
  considered up to permutation; all our relations are closed under permutations of children).
* `Hydra.Move n a b` says that `b` is obtained from `a` by one move of the game: Hercules chops
  off a head (a leaf) of `a`, and if the chopped leaf had a grandparent, `n` extra copies of the
  (already modified) parent subtree are grown at that grandparent.
* The main theorem `Frontier.Hydra_Kirby_Paris` states that there is no infinite play (for any
  choice of moves and any growth rates `k i`), and consequently that every strategy kills the
  hydra in finitely many steps.

The proof assigns to each hydra its ordinal `Hydra.ord < ε₀`, in Cantor normal form built with
the *natural* (Hessenberg) sum `♯`, and shows that every move strictly decreases this ordinal.
The key ordinal-arithmetic ingredient, proved here from scratch, is that `ω ^ b` is closed under
natural addition (`KirbyParis.nadd_lt_opow`).
-/

open Ordinal
open scoped NaturalOps

namespace KirbyParis

/-! ### Powers of `ω` are closed under natural addition -/

/-- Bookkeeping step used in `KirbyParis.key`. -/

theorem ordList_replicate_lt (h : Hydra) (k : ℕ) :
    ordList (List.replicate k h) < ω ^ Order.succ (ord h) := by
  induction k with
  | zero =>
    simp only [List.replicate_zero, ordList_nil]
    exact opow_pos _ omega0_pos
  | succ k ih =>
    rw [List.replicate_succ, ordList_cons]
    refine KirbyParis.nadd_lt_opow _ _ _ ?_ ih
    exact (opow_lt_opow_iff_right one_lt_omega0).2 (Order.lt_succ _)

/-- `Step n a b`: one move of the hydra game performed *strictly inside* `a`; that is, the chopped
leaf sits at depth at least two in `a`, so that its grandparent is a node of `a` and the
duplication of the parent (creating `n` extra copies) takes place inside `a`. -/
inductive Step (n : ℕ) : Hydra → Hydra → Prop
  | /-- The chopped leaf is at depth two: its parent `node pl` (where the children `pl` of the
    parent consist of the chopped leaf `node []` together with `cs`) is a child of the root,
    which is therefore the grandparent; after removing the leaf, the parent becomes `node cs`, and
    `n` extra copies of it are attached to the root. -/
    copy {l rest cs pl : List Hydra} (h : l.Perm (node pl :: rest))
      (hp : pl.Perm (node [] :: cs)) :
      Step n (node l) (node (List.replicate (n + 1) (node cs) ++ rest))
  | /-- The move takes place inside one of the children. -/
    cong {l rest : List Hydra} {a b : Hydra} (h : l.Perm (a :: rest)) :
      Step n a b → Step n (node l) (node (b :: rest))

/-- `Move n a b`: `b` is obtained from the hydra `a` by one move of the Kirby–Paris game with
growth rate `n`: Hercules chops off a head (a leaf) of `a`; if that leaf had a grandparent, then
`n` extra copies of the parent subtree (with the leaf already removed) are grown at the
grandparent; if the leaf was a child of the root, it simply disappears. -/
inductive Move (n : ℕ) : Hydra → Hydra → Prop
  | /-- Chopping a head attached directly to the root: nothing regrows. -/
    chop {l rest : List Hydra} (h : l.Perm (node [] :: rest)) : Move n (node l) (node rest)
  | /-- Chopping a head at depth at least two: the growth happens at its grandparent, which is a
    node of the hydra. -/
    ofStep {a b : Hydra} : Step n a b → Move n a b

/-- Every move strictly inside a hydra decreases its ordinal. -/
