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

lemma takeF_getElem (f : ℕ → A) {n i : ℕ} (h : i < n) :
    (takeF f n)[i]'(by simpa using h) = f i := by
  simp [takeF]

