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

lemma WinsFor.congr_parity {i j : ℕ} (h : i % 2 = j % 2) {S : Set (ℕ → A)} {s : List A → A}
    (hs : WinsFor i S s) : WinsFor j S s :=
  fun x hx => hs x fun n hn => hx n (by omega)

/-! ## Consistency of the framework

The two alternatives in `Determined` are mutually exclusive: any pair of strategies produces a
play consistent with both, so the two players cannot both win. -/

section Consistency

/-- The position reached after `n` moves when player `0` follows `s₀` and player `1` follows
`s₁`. -/
