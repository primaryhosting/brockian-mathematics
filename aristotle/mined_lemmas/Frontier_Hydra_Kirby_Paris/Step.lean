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

theorem Step.ord_lt {n : ℕ} {a b : Hydra} (hab : Step n a b) : ord b < ord a := by
  induction hab with
  | @copy l rest cs pl h hp =>
    rw [ord_node, ord_node, ordList_perm h, ordList_cons, ordList_append]
    refine nadd_lt_nadd_right ?_ _
    have hord : ord (node pl) = Order.succ (ord (node cs)) := by
      rw [ord_node, ordList_perm hp, ordList_cons, ord_node, ord_node, ordList_nil, opow_zero,
        nadd_comm, nadd_one]
    rw [hord]
    exact ordList_replicate_lt (node cs) (n + 1)
  | cong h _ ih =>
    rw [ord_node, ord_node, ordList_perm h, ordList_cons, ordList_cons]
    exact nadd_lt_nadd_right ((opow_lt_opow_iff_right one_lt_omega0).2 ih) _

/-- **Every move of the hydra game strictly decreases the ordinal of the hydra.** -/
