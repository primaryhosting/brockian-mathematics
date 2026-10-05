/-
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header above is repeated as a plain comment at the very top of the file: Lean 4 requires
`import` commands to precede any module docstring.)
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Brockian

/-- The wheel modulus considered here. -/

def goldbachB (n : ℕ) : Bool :=
  wheelCandidates.any (fun p => isPrimeB p && isPrimeB (n - p) && p ≤ n)

/-- `n` is a sum of two primes. -/
