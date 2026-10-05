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

theorem nadd_lt_mul_nat (c : Ordinal)
    (hIH : ∀ x y : Ordinal, x < ω ^ c → y < ω ^ c → x ♯ y < ω ^ c) (m n : ℕ) (a b : Ordinal)
    (ha : a < ω ^ c * m) (hb : b < ω ^ c * n) : a ♯ b < ω ^ c * (m + n : ℕ) := by
  match m, n with
  | 0, _ => simp at ha
  | _, 0 => simp at hb
  | (m + 1), (n + 1) =>
    obtain ⟨p, x, hp, hx, rfl⟩ := decomp c m a ha
    obtain ⟨q, y, hq, hy, rfl⟩ := decomp c n b hb
    have h1 := key c hIH _ _ p q x y hx hy rfl rfl
    have h2 : ω ^ c * (p + q : ℕ) + (x ♯ y) < ω ^ c * (p + q + 1 : ℕ) := by
      rw [Nat.cast_add (p + q) 1, Nat.cast_one, mul_add, mul_one]
      exact (add_lt_add_iff_left _).2 (hIH _ _ hx hy)
    have h3 : ω ^ c * (p + q + 1 : ℕ) ≤ ω ^ c * (m + 1 + (n + 1) : ℕ) :=
      mul_le_mul_right (Nat.cast_le.2 (by omega)) _
    exact (h1.trans_lt h2).trans_le h3

/-- **Powers of `ω` are closed under natural (Hessenberg) addition.** -/
