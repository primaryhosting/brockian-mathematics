/-
/-!
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

/-!
Every open game is determined (Gale–Stewart).

We consider the infinite two-player game on a nonempty set `A` of moves: the two players
alternately choose elements of `A`, player I moving at the even stages and player II at the odd
stages, producing a play `x : ℕ → A`.  Player I wins the play `x` iff `x ∈ W`, where `W` is the
payoff set.  A *strategy* is a function `List A → A` assigning a move to every position (finite
sequence of previous moves).

The theorem states: if `W` is open in the product topology on `ℕ → A` (with `A` discrete), then
either player I has a winning strategy or player II has one.
-/

namespace Frontier

open scoped Classical

variable {A : Type*}

/-- The list of the first `n` moves of the play `x`. -/

theorem pref_eq_iff {x y : ℕ → A} {n : ℕ} : pref x n = pref y n ↔ ∀ i < n, x i = y i := by
  constructor
  · intro h i hi
    have := congrArg (fun l => l[i]?) h
    simpa [pref, List.getElem?_map, List.getElem?_range, hi] using this
  · intro h
    simp only [pref]
    exact List.map_congr_left (by simpa using fun i hi => h i hi)

/-! ### Existence of plays -/

/-- The position after `n` moves when I plays `σ` and II plays `τ`. -/
