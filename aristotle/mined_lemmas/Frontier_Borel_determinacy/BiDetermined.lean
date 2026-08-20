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

lemma BiDetermined.compl {S : Set (ℕ → A)} (h : BiDetermined S) : BiDetermined Sᶜ :=
  ⟨h.2, by rw [compl_compl]; exact h.1⟩

variable [Nonempty A] [DiscreteTopology A]

/-- Closed sets are bi-determined. -/
