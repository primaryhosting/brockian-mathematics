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

theorem seqOpen_determinacy [Nonempty A] (S : Set (ℕ → A)) (hS : SeqOpen S) : Det S := by
  by_cases h : ∃ σ, WinI S σ
  · exact Or.inl h
  refine Or.inr ?_
  have hnil : Coop S [] := (coop_nil_iff S).2 h
  have key : ∀ p : List A, Coop S p → ∃ a, Coop S (p ++ [a]) := fun _ hp => exists_coop_move hp
  choose! τ hτ using key
  refine ⟨τ, ?_⟩
  intro x hfol
  have hcoop : ∀ n, Coop S (pref x n) := by
    intro n
    induction n with
    | zero => exact hnil
    | succ n ih =>
      rw [pref_succ]
      rcases Nat.even_or_odd n with he | ho
      · exact coop_of_move ih (by simpa using he) (x n)
      · rw [hfol n ho]
        exact hτ _ ih
  intro hxS
  obtain ⟨n, hn⟩ := hS x hxS
  refine hcoop n (iwins_of_all_extension ?_)
  intro y hy
  exact hn y (by simpa using hy)

/-! ## Comparison with the topological notions -/

