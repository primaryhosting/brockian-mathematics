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

theorem pref_eq_iff (x y : ℕ → A) (n : ℕ) : pref y n = pref x n ↔ ∀ i < n, y i = x i := by
  constructor
  · intro h i hi
    rcases isEmpty_or_nonempty A with hA | hA
    · exact (IsEmpty.false (x i)).elim
    · have h2 := congrArg (fun l => l.getD i (Classical.arbitrary A)) h
      dsimp only at h2
      rwa [pref_getD _ hi, pref_getD _ hi] at h2
  · intro h
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pref_succ, pref_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

/-- The basic open sets of the product topology: plays with a prescribed initial
position. -/
