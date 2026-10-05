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

def gwK2Check (n : Nat) : Bool :=
  gwK2Wheel.any fun p => gwIsPrime p && decide (p ≤ n) && gwIsPrime (n - p)

