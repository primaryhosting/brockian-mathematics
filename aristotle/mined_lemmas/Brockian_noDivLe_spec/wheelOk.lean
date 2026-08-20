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

def wheelOk (m : Nat) : Bool :=
  goldbachWheelK2.any (fun p => isPrimeB p && isPrimeB (2 * m - p))

/-- `checkAll k` tests `wheelOk m` for all `2 ≤ m ≤ k`. -/
