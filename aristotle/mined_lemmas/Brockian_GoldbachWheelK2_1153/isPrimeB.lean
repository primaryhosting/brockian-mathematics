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

def isPrimeB (n : ℕ) : Bool :=
  decide (2 ≤ n) && trialDivisors.all (fun d => decide (n < d * d) || decide (n % d ≠ 0))

