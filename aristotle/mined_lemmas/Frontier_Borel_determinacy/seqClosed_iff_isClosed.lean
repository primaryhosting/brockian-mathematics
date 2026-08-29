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

theorem seqClosed_iff_isClosed [TopologicalSpace A] [DiscreteTopology A] (S : Set (ℕ → A)) :
    SeqClosed S ↔ IsClosed S := by
  constructor
  · intro h
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro x hx
    have hne : ¬ ∀ n, ∃ y ∈ S, pref y n = pref x n := fun hall => hx (h x hall)
    push_neg at hne
    obtain ⟨n, hn⟩ := hne
    exact ⟨{y | pref y n = pref x n}, fun y hy hyS => hn y hyS hy, isOpen_prefixSet x n, rfl⟩
  · intro hS x hx
    by_contra hxS
    obtain ⟨n, hn⟩ := exists_prefix_subset hS.isOpen_compl hxS
    obtain ⟨y, hyS, hy⟩ := hx n
    exact hn y hy hyS

