/-!
# Goldbach Wheel K 2 631
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_631
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

/-- The list of primes used as spokes of the Goldbach wheel of modulus `631`. -/

lemma wheelTable631_sums :
    wheelTable631.map (fun pq => (pq.1 + pq.2) % 631) = List.range 631 := by decide

/-- **Goldbach wheel, `K = 2`, modulus `631`.**
Every residue class modulo `631` is represented by a sum of two primes:
for every natural number `n` there are primes `p, q` with `p + q ≡ n [MOD 631]`. -/
