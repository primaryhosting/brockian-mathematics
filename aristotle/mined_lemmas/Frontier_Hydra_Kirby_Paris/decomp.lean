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

theorem decomp (c : Ordinal) (p : ℕ) (A' : Ordinal) (h : A' < ω ^ c * (p + 1 : ℕ)) :
    ∃ p' : ℕ, ∃ x' : Ordinal, p' ≤ p ∧ x' < ω ^ c ∧ A' = ω ^ c * p' + x' := by
  have hne : (ω : Ordinal) ^ c ≠ 0 := (opow_pos c omega0_pos).ne'
  have hdiv : A' / ω ^ c < ((p + 1 : ℕ) : Ordinal) := (Ordinal.div_lt hne).2 h
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.1 (hdiv.trans (nat_lt_omega0 _))
  refine ⟨n, A' % ω ^ c, ?_, Ordinal.mod_lt _ hne, ?_⟩
  · have h' : ((n : ℕ) : Ordinal) < ((p + 1 : ℕ) : Ordinal) := hn ▸ hdiv
    have := Nat.cast_lt.1 h'
    omega
  · rw [← hn]; exact (Ordinal.div_add_mod _ _).symm

/-- Natural addition adds the leading coefficients: an upper bound version, assuming closure of
`ω ^ c` under natural addition. -/
