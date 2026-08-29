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

lemma takeF_getD [Inhabited A] (f : ℕ → A) {n i : ℕ} (h : i < n) :
    (takeF f n).getD i default = f i := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), takeF_getElem f h]

