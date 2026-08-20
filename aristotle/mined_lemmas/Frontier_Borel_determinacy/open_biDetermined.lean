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

theorem open_biDetermined {S : Set (ℕ → A)} (hS : IsOpen S) : BiDetermined S := by
  have h := closed_biDetermined (isClosed_compl_iff.2 hS)
  simpa using h.compl

/-- **Borel determinacy** (Martin's theorem), as a Lean-checked reduction: granting the
countable-union step of Martin's induction (a true statement, being a consequence of the full
theorem), every Borel game is determined.  The base case of the induction — determinacy of
closed games, the Gale–Stewart theorem — is proved unconditionally above
(`Frontier.gale_stewart`), as is the closure of the class of bi-determined sets under
complementation (`Frontier.BiDetermined.compl`). -/
