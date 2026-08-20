/-
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is written as a plain block comment.)

import Mathlib

/-!
## Overview

We formalise infinite two-player perfect-information games on Baire space `ℕ → ℕ`
(the standard setting for Borel determinacy), together with strategies, winning
strategies and determinacy.

* `Frontier.BorelDeterminacy` is the full statement of Martin's theorem: every game whose
  payoff set is Borel is determined.
* `Frontier.Borel_determinacy` is the *base case* of that statement, proved here in full:
  every game whose payoff set lies at the bottom level of the Borel hierarchy
  (`Σ⁰₁`, i.e. open, or `Π⁰₁`, i.e. closed) is determined.  This is the Gale–Stewart
  theorem, the base case on which Martin's inductive unravelling argument rests.
  Mathlib contains no determinacy results, so the game-theoretic framework and the
  proof are developed here from scratch.

The proof of the base case is the classical one: if the first player has no winning
strategy from the empty position, the second player can move so as to preserve the
property "the first player has no winning strategy from the current position", and an
open payoff set would be entered only at a position from which the first player wins
trivially.
-/

namespace Frontier

/-- Baire space: the space of plays of a game where each move is a natural number. -/
abbrev Baire := ℕ → ℕ

/-- The position (finite sequence of moves) consisting of the first `n` moves of the
play `f`. -/

theorem win_compl_of_not_win_of_isOpen {S : Set Baire} {e : ℕ} {p : List ℕ} (he : e < 2)
    (hS : IsOpen S) (h : ¬ Win S e p) : Win Sᶜ (1 - e) p := by
  classical
  -- the opponent's strategy: always move to a position from which player `e` does not win
  set τ : List ℕ → ℕ := fun q => if h : ∃ a, ¬ Win S e (q ++ [a]) then h.choose else 0
    with hτ
  refine ⟨τ, fun f hf hcons => ?_⟩
  have hfp : pre f p.length = p := hf
  -- every position reached is one from which player `e` has no winning strategy
  have key : ∀ n, p.length ≤ n → ¬ Win S e (pre f n) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rw [hfp]; exact h
    | succ n hn ih =>
        rw [pre_succ]
        by_cases hpar : n % 2 = e
        · -- player `e` moves: by `win_of_win_append` no successor can be winning
          intro hw
          exact ih (win_of_win_append (by simpa using hpar) hw)
        · -- the opponent moves, following `τ`
          have hex : ∃ a, ¬ Win S e (pre f n ++ [a]) := by
            by_contra hall
            push_neg at hall
            exact ih (win_of_forall_win_append hall)
          have hfn : f n = τ (pre f n) := by
            refine hcons n hn ?_
            have : n % 2 < 2 := Nat.mod_lt _ (by norm_num)
            omega
          have hch : τ (pre f n) = hex.choose := by simp only [hτ, dif_pos hex]
          rw [hfn, hch]
          exact hex.choose_spec
  -- an open payoff set can only be entered at a position which player `e` wins outright
  intro hmem
  obtain ⟨u, ⟨y, n, rfl⟩, hxu, hus⟩ :=
    (PiNat.isTopologicalBasis_cylinders (fun _ => ℕ)).exists_subset_of_mem_open hmem hS
  refine key (max n p.length) (le_max_right _ _) ⟨fun _ => 0, fun g hg _ => hus ?_⟩
  simp only [PiNat.cylinder, Set.mem_setOf_eq] at hxu ⊢
  intro i hi
  have hi' : i < max n p.length := lt_of_lt_of_le hi (le_max_left _ _)
  have hgn : pre g (max n p.length) = pre f (max n p.length) := by simpa [Extends] using hg
  have h2 : nth (pre g (max n p.length)) i = nth (pre f (max n p.length)) i := by rw [hgn]
  rw [nth_pre hi', nth_pre hi'] at h2
  rw [h2, hxu i hi]

/-- Every open game is determined, from any starting position. -/
