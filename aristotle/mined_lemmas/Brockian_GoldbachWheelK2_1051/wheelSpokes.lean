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

def wheelSpokes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73]

/-- A kernel-friendly primality certificate: trial division by all `m < 40` with `m * m ≤ p`.
It is sound for every `p < 1600`. -/
