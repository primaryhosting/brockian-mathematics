/-
# Hydra Kirby Paris
Category: Frontier — Set Theory
Target: Frontier.Hydra_Kirby_Paris
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

We formalize the Kirby–Paris hydra game and prove that **every** play terminates,
no matter which head Hercules chops and no matter how many copies the hydra grows
at each stage (so, in particular, for every strategy).

A hydra is a finite rooted tree, encoded as `Hydra.node : List Hydra → Hydra`.
A *head* is a leaf.  In one move Hercules chops off a head; if the head has a
grandparent, the grandparent grows `n` extra copies of the subtree hanging at the
head's parent (with the head already removed).  The number `n` may be arbitrary
and may change from move to move.

The proof is the classical one: we attach to a hydra the ordinal
`o(node [h₁,…,h_k]) = ω ^ o(h₁) ♯ ⋯ ♯ ω ^ o(h_k) < ε₀`
(`♯` is the natural / Hessenberg sum) and check that every move strictly decreases
it; well-foundedness of the ordinals then finishes the argument.

The ordinal-arithmetic input that is not in Mathlib is that `ω ^ d` is closed under
natural sums; this is proved from scratch in the first section
(`Frontier.nadd_lt_opow_omega0`).

By the Kirby–Paris theorem this termination statement is not provable in Peano
arithmetic; the proof below is of course carried out in the ambient set theory of
Lean/Mathlib, where transfinite induction below ε₀ is available.
-/

open Ordinal NaturalOps

namespace Frontier

/-! ## Part 1: `ω ^ d` is closed under natural addition -/

/-- The key estimate: natural addition of two ordinals below `W * ω` is bounded by
the "Cantor-like" expression built from their quotients and remainders modulo `W`,
provided `W` itself is closed under natural addition. -/

theorem ordList_lt_opow (d : Ordinal) (l : List Hydra) (hl : ∀ x ∈ l, ord x < d) :
    ordList l < ω ^ d := by
  induction l with
  | nil => simpa using Ordinal.opow_pos d Ordinal.omega0_pos
  | cons a t ih =>
      have ha : ω ^ ord a < ω ^ d :=
        (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2 (hl a (by simp))
      have ht : ordList t < ω ^ d := ih fun x hx => hl x (by simp [hx])
      simpa using nadd_lt_opow_omega0 d _ _ ha ht

/-! ### The moves of the game -/

/-- `ChopHead h h'`: `h'` is obtained from `h` by chopping off a head (a leaf)
which is a child of the root of `h`. -/
inductive ChopHead : Hydra → Hydra → Prop
  | mk (pre post : List Hydra) :
      ChopHead (.node (pre ++ .node [] :: post)) (.node (pre ++ post))

/-- `DeepStep n h h'`: `h'` results from `h` by chopping a head at depth `≥ 2`,
the grandparent of the chopped head growing `n` extra copies of the head's parent.

* `copy`: the chopped head lies at depth `2`, i.e. its parent `c` is a child of the
  root; the root, being the grandparent, then carries `n + 1` copies of `c` with that
  head removed (the original one, and `n` new ones).
* `deep`: the chopped head lies at depth `≥ 3`, so the whole move, copies included,
  happens inside a single child of the root. -/
inductive DeepStep (n : ℕ) : Hydra → Hydra → Prop
  | copy (pre post : List Hydra) {c c' : Hydra} : ChopHead c c' →
      DeepStep n (.node (pre ++ c :: post)) (.node (pre ++ List.replicate (n + 1) c' ++ post))
  | deep (pre post : List Hydra) {c c' : Hydra} : DeepStep n c c' →
      DeepStep n (.node (pre ++ c :: post)) (.node (pre ++ c' :: post))

/-- `Step n h h'`: `h'` results from `h` by one legal move of the hydra game in which
the hydra grows `n` extra copies.  Either Hercules chops a head attached directly to
the root (such a head has no grandparent, so nothing grows back), or he chops a head
at depth `≥ 2`, whose grandparent then grows `n` copies of the head's parent. -/
