import Mathlib

/-!
# Two Squares 41 (Mathlib version)

Supplementary file: the same statement as `Math.two_squares_41`, but phrased with Mathlib's
`Nat.Prime`. It also records that the ad hoc primality predicate used in the main file agrees
with `Nat.Prime` on `41`.
-/

namespace Math

/-- The prime `41` is a sum of two squares: `41 = 4 ^ 2 + 5 ^ 2`. -/

def IsPrimeNat (p : Nat) : Prop := 2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

/-- Every divisor of `41` is `1` or `41`. -/
