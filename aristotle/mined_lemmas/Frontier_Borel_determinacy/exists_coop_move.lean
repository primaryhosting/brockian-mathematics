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

theorem exists_coop_move [Nonempty A] {S : Set (ℕ → A)} {p : List A}
    (hp : Coop S p) : ∃ a, Coop S (p ++ [a]) := by
  by_contra hcon
  push_neg at hcon
  simp only [Coop, not_not] at hcon
  choose σ' hσ' using hcon
  refine hp ⟨fun p' => σ' (p'.getD p.length (Classical.arbitrary A)) p', ?_⟩
  intro x hx hf
  set a : A := x p.length with ha
  have hext : pref x (p ++ [a]).length = p ++ [a] := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    rw [pref_succ, hx]
  refine hσ' a x hext ?_
  intro n hn hev
  have hn' : p.length < n := by simpa [List.length_append] using hn
  have := hf n (le_of_lt hn') hev
  rw [this]
  simp only [pref_getD x hn', ha]

/-- From a position where player I has no winning strategy and player I is to move,
every move again leads to such a position. -/
