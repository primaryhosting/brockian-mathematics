/-
/-!
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

/-!
Every open game is determined (Gale–Stewart).

We consider the infinite two-player game on a nonempty set `A` of moves: the two players
alternately choose elements of `A`, player I moving at the even stages and player II at the odd
stages, producing a play `x : ℕ → A`.  Player I wins the play `x` iff `x ∈ W`, where `W` is the
payoff set.  A *strategy* is a function `List A → A` assigning a move to every position (finite
sequence of previous moves).

The theorem states: if `W` is open in the product topology on `ℕ → A` (with `A` discrete), then
either player I has a winning strategy or player II has one.
-/

namespace Frontier

open scoped Classical

variable {A : Type*}

/-- The list of the first `n` moves of the play `x`. -/

theorem gale_stewart_openPayoff [Inhabited A] (W : Set (ℕ → A)) (hW : IsOpenPayoff W) :
    (∃ σ : List A → A, ∀ x : ℕ → A, IFollows σ [] x → x ∈ W) ∨
      (∃ τ : List A → A, ∀ x : ℕ → A, IIFollows τ [] x → x ∉ W) := by
  by_cases hwin : WinI W ([] : List A)
  · obtain ⟨σ, hσ⟩ := hwin
    exact Or.inl ⟨σ, fun x hfol => hσ x rfl hfol⟩
  · right
    have hstepI : ∀ q : List A, Even q.length → ¬ WinI W q → ∀ a, ¬ WinI W (q ++ [a]) :=
      fun q hq hnq a hcon => hnq (winI_of_snoc hq hcon)
    have hstepII : ∀ r : List A, ¬ WinI W r → ∃ b, ¬ WinI W (r ++ [b]) := by
      intro r hnr
      by_contra hc
      push_neg at hc
      exact hnr (winI_of_forall_snoc hc)
    refine ⟨fun r => if h : ∃ b, ¬ WinI W (r ++ [b]) then h.choose else default,
      fun x hfol hxW => ?_⟩
    have hpos : ∀ n, ¬ WinI W (pref x n) := by
      intro n
      induction n with
      | zero => simpa using hwin
      | succ n ih =>
        rw [pref_succ]
        by_cases hn : Even n
        · exact hstepI (pref x n) (by simpa using hn) ih (x n)
        · have hex := hstepII (pref x n) ih
          -- player II's move keeps the position non-winning for player I
          have hmove := hfol n (by simp) hn
          rw [hmove]
          simp only [dif_pos hex]
          exact hex.choose_spec
    obtain ⟨n, hn⟩ := hW x hxW
    refine hpos n ⟨fun _ => default, fun y hy _ => hn y ?_⟩
    rw [length_pref] at hy
    exact fun i hi => (pref_eq_iff.mp hy) i hi

