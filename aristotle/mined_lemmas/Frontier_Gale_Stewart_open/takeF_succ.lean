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

lemma takeF_succ (f : ℕ → A) (n : ℕ) : takeF f (n + 1) = takeF f n ++ [f n] := by
  simp [takeF, List.range_succ]

