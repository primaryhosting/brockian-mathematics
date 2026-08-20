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

def FollowsI (σ : List X → X) (a : ℕ → X) : Prop := ∀ n, Even n → a n = σ (hist a n)

/-- A play `a` follows the strategy `τ` for player II (who moves at odd times). -/
