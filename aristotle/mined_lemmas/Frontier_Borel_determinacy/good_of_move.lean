import Mathlib

/-!
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Frontier

/-! ## Games on a set of moves

A play of the game is an infinite sequence `x : ℕ → A` of moves.  Player I plays the
moves `x 0, x 2, x 4, …` and player II plays the moves `x 1, x 3, x 5, …`.  Player I
wins the play `x` iff `x` belongs to the payoff set `S`.
-/

universe u

variable {A : Type u}

/-- The position (list of moves played) after the first `n` moves of the play `x`. -/

theorem good_of_move {S : Set (ℕ → A)} {p : List A}
    (hp : Good S p) (hodd : Odd p.length) (a : A) : Good S (p ++ [a]) := by
  intro ⟨τ', hτ'⟩
  refine hp ⟨fun p' => if p'.length = p.length then a else τ' p', ?_⟩
  intro x hx hf
  have hmove : x p.length = a := by
    have := hf p.length le_rfl hodd
    simpa [hx] using this
  have hext : pref x (p ++ [a]).length = p ++ [a] := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    rw [pref_succ, hx, hmove]
  refine hτ' x hext ?_
  intro n hn hodd'
  have hn' : p.length < n := by simpa [List.length_append] using hn
  have := hf n (le_of_lt hn') hodd'
  rw [this]
  simp only [pref_length]
  rw [if_neg (by omega)]

/-- A position from which no extension lies in `S` is won by player II. -/
