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

theorem winI_of_snoc {W : Set (ℕ → A)} {q : List A} {a : A}
    (heven : Even q.length) (h : WinI W (q ++ [a])) : WinI W q := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨fun r => if r = q then a else σ r, fun x hx hfol => ?_⟩
  have hmove : x q.length = a := by
    have := hfol q.length le_rfl heven
    simpa [hx] using this
  have hpref : pref x (q ++ [a]).length = q ++ [a] := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    rw [pref_succ, hx, hmove]
  refine hσ x hpref (fun n hn hne => ?_)
  have hlen : q.length + 1 ≤ n := by simpa using hn
  have hne' : pref x n ≠ q := by
    intro hcon
    have := congrArg List.length hcon
    simp at this
    omega
  have := hfol n (by omega) hne
  simpa [hne'] using this

/-! ### Determinacy -/

/-- **Gale–Stewart** for combinatorially open payoff sets. -/
