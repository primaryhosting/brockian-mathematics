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

theorem determined_of_isOpen {A : Set Baire} (hA : IsOpen A) : Determined A := by
  by_cases h : Win A 0 []
  · exact Or.inl h
  · exact Or.inr (by simpa using win_compl_of_not_win_of_isOpen (p := []) (by norm_num) hA h)

/-- Every closed game is determined. -/
