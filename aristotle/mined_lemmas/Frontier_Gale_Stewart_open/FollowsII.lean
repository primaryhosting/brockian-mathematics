/-
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace GaleStewart

universe u

variable {X : Type u}

/-- The list of the first `n` moves of the play `a`. -/

def FollowsII (τ : List X → X) (a : ℕ → X) : Prop := ∀ n, Odd n → a n = τ (hist a n)

/-- The position after `n` moves when both players follow their strategies. -/
