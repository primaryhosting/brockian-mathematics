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

theorem bound_lt (c : Ordinal)
    (hIH : ∀ x y : Ordinal, x < ω ^ c → y < ω ^ c → x ♯ y < ω ^ c)
    (p' p q : ℕ) (x' x y u : Ordinal) (hx' : x' < ω ^ c) (hy : y < ω ^ c)
    (hu : u ≤ ω ^ c * (p' + q : ℕ) + (x' ♯ y))
    (h : p' < p ∨ (p' = p ∧ x' < x)) :
    u < ω ^ c * (p + q : ℕ) + (x ♯ y) := by
  rcases h with h | ⟨rfl, hxx⟩
  · have hcast : ((p' + q + 1 : ℕ) : Ordinal) = ((p' + q : ℕ) : Ordinal) + 1 := by
      rw [Nat.cast_add, Nat.cast_one]
    have h1 : ω ^ c * (p' + q : ℕ) + (x' ♯ y) < ω ^ c * (p' + q + 1 : ℕ) := by
      rw [hcast, mul_add, mul_one]
      exact (add_lt_add_iff_left _).2 (hIH _ _ hx' hy)
    have h2 : ω ^ c * (p' + q + 1 : ℕ) ≤ ω ^ c * (p + q : ℕ) :=
      mul_le_mul_right (Nat.cast_le.2 (by omega)) _
    exact hu.trans_lt (h1.trans_le (h2.trans le_self_add))
  · exact hu.trans_lt ((add_lt_add_iff_left _).2 (nadd_lt_nadd_right hxx y))

/-- Every ordinal below `ω ^ c * (p + 1)` is of the form `ω ^ c * p' + x'` with `p' ≤ p` a natural
number and `x' < ω ^ c`. -/
