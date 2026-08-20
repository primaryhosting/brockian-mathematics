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

def playSeq (σ τ : List X → X) (n : ℕ) : X :=
  if Even n then σ (playPos σ τ n) else τ (playPos σ τ n)

