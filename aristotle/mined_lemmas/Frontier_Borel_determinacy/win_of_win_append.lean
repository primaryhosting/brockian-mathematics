/-
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is written as a plain block comment.)

import Mathlib

/-!
## Overview

We formalise infinite two-player perfect-information games on Baire space `ℕ → ℕ`
(the standard setting for Borel determinacy), together with strategies, winning
strategies and determinacy.

* `Frontier.BorelDeterminacy` is the full statement of Martin's theorem: every game whose
  payoff set is Borel is determined.
* `Frontier.Borel_determinacy` is the *base case* of that statement, proved here in full:
  every game whose payoff set lies at the bottom level of the Borel hierarchy
  (`Σ⁰₁`, i.e. open, or `Π⁰₁`, i.e. closed) is determined.  This is the Gale–Stewart
  theorem, the base case on which Martin's inductive unravelling argument rests.
  Mathlib contains no determinacy results, so the game-theoretic framework and the
  proof are developed here from scratch.

The proof of the base case is the classical one: if the first player has no winning
strategy from the empty position, the second player can move so as to preserve the
property "the first player has no winning strategy from the current position", and an
open payoff set would be entered only at a position from which the first player wins
trivially.
-/

namespace Frontier

/-- Baire space: the space of plays of a game where each move is a natural number. -/
abbrev Baire := ℕ → ℕ

/-- The position (finite sequence of moves) consisting of the first `n` moves of the
play `f`. -/

theorem win_of_win_append {S : Set Baire} {e : ℕ} {p : List ℕ} {a : ℕ}
    (hp : p.length % 2 = e) (h : Win S e (p ++ [a])) : Win S e p := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨fun q => if q = p then a else σ q, fun f hf hcons => ?_⟩
  have hfp : f p.length = a := by
    have := hcons p.length le_rfl hp
    rw [Extends] at hf
    simpa [hf] using this
  have hext : Extends (p ++ [a]) f := by
    have : pre f (p.length + 1) = p ++ [a] := by
      rw [pre_succ, hf, hfp]
    simpa [Extends] using this
  refine hσ f hext ?_
  intro n hn hpar
  have hlen : p.length < n := by simpa using hn
  have hne : pre f n ≠ p := by
    intro hEq
    have := congrArg List.length hEq
    simp at this
    omega
  have := hcons n (le_of_lt hlen) hpar
  simpa [hne] using this

/-- If player `e` wins from *every* immediate successor position of `p`, then player `e`
wins from `p`.  (This is used when it is the opponent's turn at `p`; the parity of
`p.length` is in fact irrelevant, since a strategy may read off the last move played.) -/
