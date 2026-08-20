/-!
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QI

open Finset

/-- The sign `(-1)^(f x)` attached to a Boolean value. -/

lemma djAmp_eq {n : ℕ} (f : (Fin n → Bool) → Bool) :
    djAmp f = (2 ^ n - 2 * (numTrue f : ℚ)) / 2 ^ n := by
  rw [djAmp, djSum_eq]

