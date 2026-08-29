/-!
# Goldbach Wheel K 2 1153
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1153
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxRecDepth 100000

namespace Brockian

/-- Candidate divisors `2, 3, …, 47`: enough to certify primality below `48^2 = 2304`. -/

def wheel : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73]

/-- `goodB N` checks that `N` is the sum of a wheel prime and another prime. -/
