import Mathlib

/-!
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

universe u

variable {A : Type u}

/-! ## The game framework

We consider infinite two–player games on a set `A` of moves.  A *play* is a sequence
`x : ℕ → A`; player `0` chooses the moves `x n` with `n` even, player `1` chooses the moves
`x n` with `n` odd.  A *strategy* is a function `List A → A` assigning a move to every finite
position (the player only consults it at their own turns). -/

/-- The length-`n` initial segment of a play. -/

lemma exists_strategy_of_not_oppWins (i : ℕ) (T : List A → Prop) (h : ¬ OppWins i T []) :
    ∃ s : List A → A, ∀ x : ℕ → A, Follows i s x → ∀ n, T (pre x n) := by
  classical
  haveI : Inhabited A := Classical.inhabited_of_nonempty inferInstance
  refine ⟨fun p => if hp : ∃ a, ¬ OppWins i T (p ++ [a]) then hp.choose else default, ?_⟩
  intro x hx
  have key : ∀ n, ¬ OppWins i T (pre x n) := by
    intro n
    induction n with
    | zero => simpa using h
    | succ n ih =>
      rw [pre_succ]
      by_cases hturn : n % 2 = i % 2
      · have hex : ∃ a, ¬ OppWins i T (pre x n ++ [a]) := by
          by_contra hcon
          push_neg at hcon
          exact ih (OppWins.all (by simpa using hturn) hcon)
        rw [hx n hturn]
        simp only [dif_pos hex]
        exact hex.choose_spec
      · intro hw
        exact ih (OppWins.move (x n) (by simpa using hturn) hw)
  intro n
  by_contra hT
  exact key n (OppWins.out hT)

/-- If the opponent of `i` wins from the position `p`, they have a strategy which, against any
play extending `p`, forces the play out of the tree `T`. -/
