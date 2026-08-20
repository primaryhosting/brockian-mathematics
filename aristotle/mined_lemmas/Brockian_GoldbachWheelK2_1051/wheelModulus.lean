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

def wheelModulus : Nat := 1051

/-- Primality of a natural number, spelled out by trial division:
`n` is at least `2` and no `m` with `2 ≤ m < n` divides `n`. -/
