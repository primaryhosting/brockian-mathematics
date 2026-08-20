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

theorem not_both_win (S : Set (ℕ → A)) :
    ¬ ((∃ s, WinsFor 0 S s) ∧ (∃ s, WinsFor 1 Sᶜ s)) := by
  rintro ⟨⟨s₀, h₀⟩, ⟨s₁, h₁⟩⟩
  exact h₁ _ (follows_playOut_one s₀ s₁) (h₀ _ (follows_playOut_zero s₀ s₁))

end Consistency

/-! ## The Gale–Stewart theorem (the base case of Martin's theorem)

A game whose payoff set is closed (in the product topology, `A` discrete) is determined.
This is proved via an inductively defined predicate describing the positions from which the
player *aiming to leave the tree* wins. -/

section GaleStewart

/-- `OppWins i T p` : from the position `p`, the opponent of player `i` can force the play to
leave the tree `T` (player `i` moves at positions of length `≡ i [MOD 2]`). -/
inductive OppWins (i : ℕ) (T : List A → Prop) : List A → Prop
  | out {p : List A} : ¬ T p → OppWins i T p
  | move {p : List A} (a : A) :
      p.length % 2 ≠ i % 2 → OppWins i T (p ++ [a]) → OppWins i T p
  | all {p : List A} :
      p.length % 2 = i % 2 → (∀ a : A, OppWins i T (p ++ [a])) → OppWins i T p

variable [Nonempty A]

/-- If the opponent of `i` does not win from the empty position, player `i` has a strategy
keeping the play inside the tree `T` forever. -/
