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

theorem coop_nil_iff (S : Set (ℕ → A)) : Coop S [] ↔ ¬ ∃ σ, WinI S σ := by
  unfold Coop Iwins WinIfrom WinI FollowsI
  simp [pref]

/-- If player I wins from every one-move extension of `p`, then player I wins from `p`. -/
