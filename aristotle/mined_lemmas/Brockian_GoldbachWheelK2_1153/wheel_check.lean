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

theorem wheel_check : ((List.range' 2 1152).all (fun n => goodB (2 * n))) = true := by decide

/-- **Goldbach with wheel modulus 1153, K = 2.**
For every `n` with `2 ≤ n ≤ 1153`, the even number `2 * n` is a sum of two primes,
where the smaller summand can be chosen from the wheel of primes up to `73`. -/
