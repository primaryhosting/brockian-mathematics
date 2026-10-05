/-!
# Goldbach Wheel K 2 1051
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1051
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- Primality, stated in the usual way: `p` is at least `2` and its only divisors are
`1` and `p`. (This file is self-contained, so the predicate is spelled out here.) -/

def gwNoSmallDiv (p : Nat) : Bool :=
  (List.range 33).all fun d => decide (d < 2) || decide (p < d * d) || decide (p % d ≠ 0)

/-- Boolean primality test, sound for arguments `p ≤ 1051`. -/
