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


set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Brockian

/-- `wheelWitnessK2` is a table of small "wheel" primes: entry `i` is the least prime `p`
such that both `p` and `2 * i - p` are prime (and `0` for `i < 2`). -/

def wheelSmallK2 (n : Nat) : Nat := wheelWitnessK2.getD (n / 2) 0

/-- Certified check of the whole table: for every index `2 ≤ i < 526`, the tabulated value
`p` is prime, `2 * i - p` is prime, `p ≤ 2 * i`, and `p ≤ 73`. -/
