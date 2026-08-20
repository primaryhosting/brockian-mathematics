import Mathlib

/-!
# Goldbach Wheel K 2 1051
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1051
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace Brockian

/-- Trial division helper: `noFactorFrom f d n` is `true` when none of
`d, d+1, …` (up to `f` steps, stopping as soon as the divisor squared exceeds `n`)
divides `n`. -/

theorem wheelTable : ∀ m ∈ Finset.Icc 5 525,
    ∃ p ∈ ([5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73] : List ℕ),
      primeB p = true ∧ primeB (2 * m - p) = true ∧ p + (2 * m - p) = 2 * m ∧
        (p % 6 = 1 ∨ p % 6 = 5) ∧ ((2 * m - p) % 6 = 1 ∨ (2 * m - p) % 6 = 5) := by decide

/--
**Goldbach Wheel, K = 2, bound 1051.**

Two statements about the even numbers up to `1051`:

* every even `n` with `4 ≤ n ≤ 1051` is a sum of two primes;
* (wheel refinement for the `K = 2` wheel, i.e. modulus `2 * 3 = 6`) every even `n`
  with `10 ≤ n ≤ 1051` is a sum of two primes *both coprime to `6`*, i.e. both lying
  on the wheel of the first two primes. (The bound `10` is sharp: `4 = 2 + 2`,
  `6 = 3 + 3` and `8 = 3 + 5` all need a prime dividing `6`.)
-/
