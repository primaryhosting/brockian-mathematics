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

def Determined (S : Set (ℕ → A)) : Prop :=
  (∃ s, WinsFor 0 S s) ∨ (∃ s, WinsFor 1 Sᶜ s)

/-- Both games attached to `S` are determined: the one in which player `0` wants the play in
`S`, and the one in which player `0` wants the play outside `S`.  (Determinacy of a single
game is not preserved by complementation, so this symmetric notion is the one that behaves
well along the Borel hierarchy.) -/
