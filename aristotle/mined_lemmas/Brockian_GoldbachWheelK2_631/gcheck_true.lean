/-
# Goldbach Wheel K 2 631
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_631
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Wheel K 2 631
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_631
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-! ### A kernel-friendly primality test

Mathlib's `Nat.decidablePrime` instance tests every candidate divisor below `n`, which makes
`by decide` too slow for a few hundred numbers of size ~1300.  We therefore use trial division by
the divisors `d` with `d * d ≤ n`, together with the correctness lemma `isPrimeB_prime`. -/

/-- `trialDivB n k = true` iff no `d ≤ k` with `2 ≤ d` and `d * d ≤ n` divides `n`. -/

lemma gcheck_true : gcheck = true := by decide

/-- **Goldbach wheel, `K = 2`, modulus `631`.**  Every even number `n` with
`4 ≤ n ≤ 2 * 631 = 1262` is a sum of two primes.  (`K = 2`: two prime summands; the wheel
modulus `631` fixes the verified range `2 * 631`.) -/
