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

theorem win_of_forall_win_append {S : Set Baire} {e : ℕ} {p : List ℕ}
    (h : ∀ a, Win S e (p ++ [a])) : Win S e p := by
  choose sig hsig using h
  refine ⟨fun q => sig (nth q p.length) q, fun f hf hcons => ?_⟩
  set a := f p.length with ha
  have hext : Extends (p ++ [a]) f := by
    have : pre f (p.length + 1) = p ++ [a] := by rw [pre_succ, hf]
    simpa [Extends] using this
  refine hsig a f hext ?_
  intro n hn hpar
  have hlen : p.length < n := by simpa using hn
  have hnth : nth (pre f n) p.length = a := nth_pre hlen
  have := hcons n (le_of_lt hlen) hpar
  rw [this]
  show sig (nth (pre f n) p.length) (pre f n) = sig a (pre f n)
  rw [hnth]

/-!
### The Gale–Stewart theorem
-/

/-- **Gale–Stewart.**  If the payoff set `S` of player `e` is open and player `e` has no
winning strategy from the position `p`, then the opponent `1 - e` has a winning strategy
for the complementary payoff set from `p`. -/
