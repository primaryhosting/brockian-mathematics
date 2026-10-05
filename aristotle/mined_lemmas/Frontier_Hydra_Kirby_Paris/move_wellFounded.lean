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

theorem move_wellFounded (n : ℕ) : WellFounded (fun b a => Move n a b) :=
  Subrelation.wf (fun h => h.ord_lt) (InvImage.wf ord Ordinal.lt_wf)

/-! ### Sanity checks -/

example : ord (node []) = 0 := rfl

example : ord (node [node []]) = 1 := by simp [ord, ordList]

/-- Chopping a head attached to the root: it simply disappears. -/
example : Move 5 (node [node [], node [node []]]) (node [node [node []]]) :=
  Move.chop (List.Perm.refl _)

/-- Chopping the top of a path of length two with growth rate `2`: the parent (now a bare head)
is triplicated at the root. -/
example : Move 2 (node [node [node []]]) (node [node [], node [], node []]) :=
  Move.ofStep (Step.copy (List.Perm.refl _) (List.Perm.refl _))

/-- The hydra obtained after `N` moves of the strategy `σ`, starting from `h₀`. -/
