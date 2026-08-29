/-
# Goldbach Wheel K 2 1153
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1153
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option autoImplicit false

namespace Brockian

/-- The list of all primes below the wheel modulus `1153`. -/

theorem prime_of_mem_wheelPrimes1153 : ∀ p ∈ wheelPrimes1153, Nat.Prime p := by
  intro p hp
  fin_cases hp <;> norm_num

set_option maxRecDepth 100000 in
/-- The exhaustive finite search: for every `k < 575`, the even number `2 * k + 4` splits as a
sum of two entries of `wheelPrimes1153`. -/
