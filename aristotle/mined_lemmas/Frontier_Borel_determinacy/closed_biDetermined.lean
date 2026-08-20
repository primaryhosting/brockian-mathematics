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

theorem closed_biDetermined {S : Set (ℕ → A)} (hS : IsClosed S) : BiDetermined S := by
  refine ⟨gale_stewart 0 hS, ?_⟩
  rcases gale_stewart 1 hS with ⟨s, hs⟩ | ⟨s, hs⟩
  · right
    exact ⟨s, by rw [compl_compl]; exact hs⟩
  · left
    exact ⟨s, hs.congr_parity (by norm_num)⟩

/-- Open sets are bi-determined. -/
