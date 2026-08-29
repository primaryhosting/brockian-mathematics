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

@[simp] lemma takeF_length (f : ℕ → A) (n : ℕ) : (takeF f n).length = n := by
  simp [takeF]

