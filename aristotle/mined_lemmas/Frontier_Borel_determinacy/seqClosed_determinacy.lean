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

theorem seqClosed_determinacy [Nonempty A] (S : Set (ℕ → A)) (hS : SeqClosed S) : Det S := by
  by_cases h : ∃ τ, WinII S τ
  · exact Or.inr h
  refine Or.inl ?_
  have hnil : Good S [] := (good_nil_iff S).2 h
  have key : ∀ p : List A, Good S p → ∃ a, Good S (p ++ [a]) := fun _ hp => exists_good_move hp
  choose! σ hσ using key
  refine ⟨σ, ?_⟩
  intro x hfol
  have hgood : ∀ n, Good S (pref x n) := by
    intro n
    induction n with
    | zero => exact hnil
    | succ n ih =>
      rw [pref_succ]
      rcases Nat.even_or_odd n with he | ho
      · rw [hfol n he]
        exact hσ _ ih
      · exact good_of_move ih (by simpa using ho) (x n)
  refine hS x ?_
  intro n
  by_contra hcon
  push_neg at hcon
  refine hgood n (iiwins_of_no_extension ?_)
  intro y hy
  exact fun hyS => hcon y hyS (by simpa using hy)

/-! ### The dual argument: open games are determined -/

/-- `σ` is a winning strategy for player I in the game with payoff `S` played from the
position `p` onwards. -/
