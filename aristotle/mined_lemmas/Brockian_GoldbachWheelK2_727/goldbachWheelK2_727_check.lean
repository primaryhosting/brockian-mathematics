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
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000000

namespace Brockian

/-- `trialDivB n f d` performs trial division of `n` by the successive divisors
`d, d+1, ...` (using at most `f` steps), stopping successfully as soon as the
divisor exceeds `√n`. It returns `true` only when no divisor `≥ d` with
`k * k ≤ n` divides `n`. -/

theorem goldbachWheelK2_727_check :
    ∀ n ∈ Finset.Icc 4 1454, n % 2 = 0 →
      ∃ p ∈ Finset.range 100, isPrimeB p ∧ isPrimeB (n - p) := by
  decide

/-- **Goldbach wheel of order `K = 2` at the modulus `727`.**
Every even `n` with `4 ≤ n ≤ 2 * 727` is a sum of two primes, and the smaller
summand can always be taken from the wheel of primes below `100`. -/
