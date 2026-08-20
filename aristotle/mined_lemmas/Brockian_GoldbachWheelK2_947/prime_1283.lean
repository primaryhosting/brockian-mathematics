/-
Primality certificates for the primes occurring in the level-2 Goldbach wheel
witness table for the modulus `947`.

These are auxiliary facts used by `Brockian.GoldbachWheelK2_947`.
-/
import Mathlib.Tactic.NormNum.Prime

namespace Brockian.Wheel


theorem prime_1283 : Nat.Prime 1283 := by norm_num
