/-!
# Goldbach Wheel K 2 1051
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1051
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Brockian

/-- The wheel modulus of this member of the `GoldbachWheelK2` family. -/

theorem wheelPrimes_prime : ∀ p ∈ wheelPrimes, IsPrimeNat p := by decide

/-- The arithmetical core of the Goldbach verification: for every `k < 524`,
the even number `2 * k + 4` is a sum of two entries of the wheel. -/
