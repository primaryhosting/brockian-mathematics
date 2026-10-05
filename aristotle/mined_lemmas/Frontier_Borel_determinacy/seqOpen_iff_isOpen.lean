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

theorem seqOpen_iff_isOpen [TopologicalSpace A] [DiscreteTopology A] (S : Set (ℕ → A)) :
    SeqOpen S ↔ IsOpen S := by
  constructor
  · intro h
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨n, hn⟩ := h x hx
    exact ⟨{y | pref y n = pref x n}, hn, isOpen_prefixSet x n, rfl⟩
  · intro hS x hx
    exact exists_prefix_subset hS hx

/-- **Gale–Stewart theorem**: every closed game is determined.  (Here `ℕ → A` carries the
product of the discrete topology on the set `A` of moves.) -/
