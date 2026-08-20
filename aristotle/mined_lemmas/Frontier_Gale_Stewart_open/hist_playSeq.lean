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

lemma hist_playSeq (σ τ : List X → X) (n : ℕ) : hist (playSeq σ τ) n = playPos σ τ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [hist, playPos, ih, playSeq]

/-- Any pair of strategies produces a play following both. -/
