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

theorem not_winning_both {W : Set (ℕ → A)} (σ τ : List A → A)
    (hσ : ∀ x : ℕ → A, IFollows σ [] x → x ∈ W)
    (hτ : ∀ x : ℕ → A, IIFollows τ [] x → x ∉ W) : False := by
  obtain ⟨x, hI, hII⟩ := exists_play σ τ
  exact hτ x hII (hσ x hI)

/-! ### The key combinatorial lemmas -/

/-- If player I wins from every one-move extension of the position `r`, he wins from `r`.
(This is used for positions `r` where it is player II's turn; the parity of `r.length` turns out
to be irrelevant.) -/
