/-
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to be the first command, so the header above is written as a
-- plain block comment; the identical text is repeated as a module docstring below.)

import Mathlib

/-!
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-- Trial divisors: all primes below `41`.  A number `m < 41 ^ 2 = 1681` is prime iff it is
at least `2` and is not divisible by any of these (other than possibly being one of them). -/

def isPrimeB (m : ℕ) : Bool :=
  decide (2 ≤ m) && trialDivisors.all (fun d => d == m || !(m % d == 0))

/-- The primes used as the small summand in the Goldbach decompositions of the wheel. -/
