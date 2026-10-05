import Mathlib

/-!
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

variable {A : Type*}

/-- The list of the first `n` moves of the play `f`. -/

def playAux (σ τ : Strategy A) : ℕ → List A
  | 0 => []
  | n + 1 => playAux σ τ n ++
      [if Even (playAux σ τ n).length then σ (playAux σ τ n) else τ (playAux σ τ n)]

