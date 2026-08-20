/-
# Goldbach Wheel K 2 631
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_631
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Wheel K 2 631
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_631
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Brockian

/-- The `K = 2` Goldbach property: `n` is a sum of two prime numbers. -/

def GoldbachK2 (n : ℕ) : Prop := ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n

/-- Decidable, finitely checkable form of the wheel statement for the modulus `631`:
for every even `n` in the window `[4, 631]` there is a prime `p ≤ 631` such that
`n - p` is again prime. -/
