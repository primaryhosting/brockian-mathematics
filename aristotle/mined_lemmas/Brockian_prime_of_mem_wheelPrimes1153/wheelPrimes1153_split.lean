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

theorem wheelPrimes1153_split :
    ∀ k ∈ List.range 575, ∃ p ∈ wheelPrimes1153, (2 * k + 4 - p) ∈ wheelPrimes1153 := by
  decide +kernel

/-- **Goldbach wheel, `K = 2`, modulus `1153`.**
Every even natural number `n` with `4 ≤ n ≤ 1153` is a sum of two primes. -/
