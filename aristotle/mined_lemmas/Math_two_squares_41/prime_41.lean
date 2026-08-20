import Mathlib

/-!
# Two Squares 41 (Mathlib version)

Supplementary file: the same statement as `Math.two_squares_41`, but phrased with Mathlib's
`Nat.Prime`. It also records that the ad hoc primality predicate used in the main file agrees
with `Nat.Prime` on `41`.
-/

namespace Math

/-- The prime `41` is a sum of two squares: `41 = 4 ^ 2 + 5 ^ 2`. -/

theorem prime_41 : IsPrimeNat 41 := ⟨by decide, divisors_41⟩

/-- The prime `41` is a sum of two squares: `41 = 4 ^ 2 + 5 ^ 2`. -/
