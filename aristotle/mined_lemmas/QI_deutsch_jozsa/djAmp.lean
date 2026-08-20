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

def djAmp {n : ℕ} (f : (Fin n → Bool) → Bool) : ℚ :=
  (∑ x : Fin n → Bool, sign (f x)) / 2 ^ n

/-- `f` is constant. -/
