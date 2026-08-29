import Mathlib

/-!
# Goldbach Wheel K 2 1051
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1051
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


set_option maxRecDepth 100000

namespace Brockian

/-- The "spokes" of the wheel: the small primes that are used as the smaller summand
in the Goldbach decompositions below.  (For every even `n ≤ 1051` one of these works.) -/

def isPrimeCert (p : ℕ) : Bool :=
  decide (2 ≤ p) && ((List.range 40).all fun m => !(decide (2 ≤ m) && decide (m * m ≤ p) && (p % m == 0)))

