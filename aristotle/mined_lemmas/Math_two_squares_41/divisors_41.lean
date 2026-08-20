import Mathlib

/-!
# Two Squares 41 (Mathlib version)

Supplementary file: the same statement as `Math.two_squares_41`, but phrased with Mathlib's
`Nat.Prime`. It also records that the ad hoc primality predicate used in the main file agrees
with `Nat.Prime` on `41`.
-/

namespace Math

/-- The prime `41` is a sum of two squares: `41 = 4 ^ 2 + 5 ^ 2`. -/

theorem divisors_41 : ∀ d : Nat, d ∣ 41 → d = 1 ∨ d = 41 := by
  intro d hd
  have hlt : d < 42 := Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hd)
  revert hd
  revert hlt
  revert d
  decide

/-- `41` is prime. -/
