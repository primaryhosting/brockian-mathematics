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

lemma eq_of_pre_eq {x y : ℕ → A} {n k : ℕ} (h : pre y n = pre x n) (hk : k < n) : y k = x k := by
  have h1 : (pre y n).getD k (y k) = y k := pre_getD y hk (y k)
  have h2 : (pre x n).getD k (y k) = x k := pre_getD x hk (y k)
  rw [← h1, h, h2]

