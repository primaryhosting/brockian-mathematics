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

theorem key (c : Ordinal) (hIH : ∀ x y : Ordinal, x < ω ^ c → y < ω ^ c → x ♯ y < ω ^ c) :
    ∀ A B : Ordinal, ∀ p q : ℕ, ∀ x y : Ordinal, x < ω ^ c → y < ω ^ c →
      A = ω ^ c * p + x → B = ω ^ c * q + y → A ♯ B ≤ ω ^ c * (p + q : ℕ) + (x ♯ y) := by
  intro A
  induction A using Ordinal.induction with
  | _ A IHA =>
    intro B
    induction B using Ordinal.induction with
    | _ B IHB =>
      intro p q x y hx hy hA hB
      have hAlt : A < ω ^ c * (p + 1 : ℕ) := by
        rw [hA, Nat.cast_add, Nat.cast_one, mul_add, mul_one]
        exact (add_lt_add_iff_left _).2 hx
      have hBlt : B < ω ^ c * (q + 1 : ℕ) := by
        rw [hB, Nat.cast_add, Nat.cast_one, mul_add, mul_one]
        exact (add_lt_add_iff_left _).2 hy
      rw [nadd_le_iff]
      constructor
      · intro A' hA'
        obtain ⟨p', x', hp', hx', rfl⟩ := decomp c p A' (hA'.trans hAlt)
        have hub := IHA _ hA' B p' q x' y hx' hy rfl hB
        refine bound_lt c hIH p' p q x' x y _ hx' hy hub ?_
        rcases lt_or_eq_of_le hp' with h | rfl
        · exact Or.inl h
        · refine Or.inr ⟨rfl, ?_⟩
          rw [hA] at hA'
          exact (add_lt_add_iff_left _).1 hA'
      · intro B' hB'
        obtain ⟨q', y', hq', hy', rfl⟩ := decomp c q B' (hB'.trans hBlt)
        have hub := IHB _ hB' p q' x y' hx hy' hA rfl
        rw [nadd_comm A _, nadd_comm x y', Nat.add_comm p q'] at hub
        rw [nadd_comm A _, nadd_comm x y, Nat.add_comm p q]
        refine bound_lt c hIH q' q p y' y x _ hy' hx hub ?_
        rcases lt_or_eq_of_le hq' with h | rfl
        · exact Or.inl h
        · refine Or.inr ⟨rfl, ?_⟩
          rw [hB] at hB'
          exact (add_lt_add_iff_left _).1 hB'

/-- Assuming `ω ^ c` is closed under natural addition, natural addition adds the multiplicities of
`ω ^ c`. -/
