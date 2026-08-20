/-
# Goldbach Wheel K 2 1153
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1153
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian

/-- Key intermediate lemma: the wheel partner `2293 = 2 * 1153 - 13` is prime. -/

lemma prime_2293 : Nat.Prime 2293 := by norm_num

/-- Auxiliary: an odd prime is exactly a prime that is coprime to the wheel modulus `2`. -/
