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

def noDivLe (n : Nat) : Nat → Bool
  | 0 => true
  | 1 => true
  | (d + 2) => (decide (n < (d + 2) * (d + 2)) || n % (d + 2) != 0) && noDivLe n (d + 1)

/-- A kernel-friendly primality test; it is correct for `n ≤ 1520`. -/
