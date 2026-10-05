import Mathlib
import RequestProject.GoldbachWheelK2_1051

/-!
# Bridge: the import-free primality predicate agrees with `Nat.Prime`

`RequestProject/GoldbachWheelK2_1051.lean` is import-free (so that the required header comment
is the first thing in the file) and therefore uses its own definition `Brockian.IsPrime`.
Here we check that this predicate is literally `Nat.Prime`, and restate the main theorem
in Mathlib's vocabulary.
-/

namespace Brockian


theorem isPrime_iff_nat_prime (n : ℕ) : IsPrime n ↔ Nat.Prime n := by
  rw [Nat.prime_def]
  rfl

/-- Mathlib-flavoured restatement of `Brockian.GoldbachWheelK2_1051`: every even `m` with
`4 ≤ m ≤ 2 * 1051` is a sum of two primes. -/
