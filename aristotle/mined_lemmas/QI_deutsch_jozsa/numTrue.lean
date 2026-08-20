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

def numTrue {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  (univ.filter fun x => f x = true).card

/-- The amplitude of the all-zeros outcome after the Deutsch–Jozsa circuit
(one oracle query, Hadamards before and after):
`2⁻ⁿ ∑_x (-1)^(f x)`. -/
