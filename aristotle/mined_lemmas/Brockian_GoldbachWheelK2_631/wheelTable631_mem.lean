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

lemma wheelTable631_mem :
    ∀ pq ∈ wheelTable631, pq.1 ∈ wheelPrimes631 ∧ pq.2 ∈ wheelPrimes631 := by decide

/-- The sums of the table entries run through all residues modulo `631`. -/
