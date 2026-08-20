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

@[simp] lemma hist_succ (a : ℕ → X) (n : ℕ) : hist a (n + 1) = hist a n ++ [a n] := rfl

