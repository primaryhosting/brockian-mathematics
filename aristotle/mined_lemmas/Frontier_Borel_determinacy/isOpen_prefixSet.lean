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

theorem isOpen_prefixSet [TopologicalSpace A] [DiscreteTopology A] (x : ℕ → A) (n : ℕ) :
    IsOpen {y : ℕ → A | pref y n = pref x n} := by
  have : {y : ℕ → A | pref y n = pref x n}
      = ⋂ i ∈ Finset.range n, (fun y : ℕ → A => y i) ⁻¹' {x i} := by
    ext y
    simp [pref_eq_iff]
  rw [this]
  refine isOpen_biInter_finset ?_
  intro i _
  exact (continuous_apply i).isOpen_preimage _ (isOpen_discrete _)

/-- Membership in an open set is determined by a finite initial position. -/
