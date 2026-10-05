/-!
# Goldbach Wheel K 2 1153
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1153
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- Primality of a natural number, stated from first principles:
`n` is at least `2` and its only divisors are `1` and `n`. -/

theorem goldbach_wheel_data :
    ∀ m ∈ List.range 577, 2 ≤ m →
      ∃ p ∈ List.range 100, wheelPrime p = true ∧ wheelPrime (2 * m - p) = true := by
  decide

/-- **Goldbach's conjecture below the wheel modulus 1153**: every even natural number
`n` with `4 ≤ n ≤ 1153` is a sum of two primes. -/
