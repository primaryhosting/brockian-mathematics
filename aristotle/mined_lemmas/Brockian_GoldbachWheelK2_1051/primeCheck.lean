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

def primeCheck (n : Nat) : Bool :=
  decide (2 ≤ n) && (List.range n).all (fun m => decide (m < 2) || decide (n % m ≠ 0))

