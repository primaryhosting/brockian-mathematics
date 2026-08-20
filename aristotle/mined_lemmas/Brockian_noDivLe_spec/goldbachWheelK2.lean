/-!
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 40000
set_option autoImplicit false

namespace Brockian

/-- Primality of a natural number, spelled out. This is equivalent to `Nat.Prime`; the
equivalence and a Mathlib-phrased restatement are in `RequestProject.Main`. -/

def goldbachWheelK2 : List Nat := [2, 3, 5, 7, 17, 19, 43, 101, 127, 149, 167, 181]

/-- `wheelOk m` tests that `2 * m = p + q` for some wheel prime `p` and some prime `q`. -/
