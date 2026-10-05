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

theorem exists_prefix_subset [TopologicalSpace A] [DiscreteTopology A] {U : Set (ℕ → A)}
    (hU : IsOpen U) {x : ℕ → A} (hx : x ∈ U) : ∃ n, ∀ y, pref y n = pref x n → y ∈ U := by
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.1 hU x hx
  refine ⟨I.sup id + 1, fun y hy => hsub ?_⟩
  intro i hi
  have hlt : i < I.sup id + 1 := Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  have : y i = x i := (pref_eq_iff x y _).1 hy i hlt
  rw [this]
  exact (hu i hi).2

