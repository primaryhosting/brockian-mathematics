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

theorem exists_spoke_dvd : ∀ q ∈ List.range 37, 2 ≤ q → ∃ p ∈ wheelSpokes, p ∣ q := by
  decide

/-- If the wheel test succeeds on `n < 1369`, then `n` has no divisor `q` with
`2 ≤ q ≤ 36` and `q < n`. -/
