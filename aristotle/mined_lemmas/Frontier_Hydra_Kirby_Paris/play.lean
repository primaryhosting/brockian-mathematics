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

def play (σ : ℕ → Hydra → Hydra) (h₀ : Hydra) : ℕ → Hydra
  | 0 => h₀
  | N + 1 => σ N (play σ h₀ N)

end Hydra

namespace Frontier

open Hydra

/-- **Kirby–Paris hydra theorem.**

1. There is no infinite play of the hydra game: for any sequence of hydras `f` and any sequence of
   growth rates `k`, it is impossible that `f (i+1)` results from `f i` by a legal move for all
   `i`.
2. Consequently every strategy `σ` (which, from any hydra other than the dead hydra `node []`,
   plays a legal move) kills the hydra after finitely many steps.

This is the Kirby–Paris theorem, whose statement is not provable in Peano arithmetic; the proof
here is the standard ordinal argument, carried out in ZFC via `Hydra.ord`. -/
