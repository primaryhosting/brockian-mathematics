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

def playPos (σ τ : List X → X) : ℕ → List X
  | 0 => []
  | n + 1 => playPos σ τ n ++ [if Even n then σ (playPos σ τ n) else τ (playPos σ τ n)]

/-- The play resulting from `σ` and `τ`. -/
