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

theorem wheel_pair_core :
    ∀ k ∈ List.range 524, ∃ p ∈ wheelPrimes, ∃ q ∈ wheelPrimes, p + q = 2 * k + 4 := by decide

/-- Goldbach's binary conjecture, verified for every even number up to the wheel
modulus `1051`. -/
