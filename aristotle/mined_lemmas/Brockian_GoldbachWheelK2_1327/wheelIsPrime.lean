import Mathlib

/-!
# Goldbach Wheel K 2 1327
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1327
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-- The primes below `41`; a trial-division wheel sufficient to decide primality
below `41 ^ 2 = 1681`. -/

def wheelIsPrime (n : ℕ) : Bool :=
  1 < n && wheelPrimes.all (fun d => decide (n < d * d) || !(n % d == 0))

/-- Boolean Goldbach check: `n` is small, odd, or a sum of two primes. -/
