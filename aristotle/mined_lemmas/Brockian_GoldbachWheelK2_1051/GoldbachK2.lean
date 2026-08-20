/-
# Goldbach Wheel K 2 1051
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1051
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Wheel K 2 1051
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1051
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- The binary (`K = 2`) Goldbach property: `n` is a sum of two primes. -/

def GoldbachK2 (n : ℕ) : Prop := ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n

/-- Convenience constructor: if `p` and `n - p` are prime and `p ≤ n`, then `n` is a sum of
two primes. -/
