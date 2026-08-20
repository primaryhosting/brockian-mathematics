/-
Primality certificates for the primes occurring in the level-2 Goldbach wheel
witness table for the modulus `947`.

These are auxiliary facts used by `Brockian.GoldbachWheelK2_947`.
-/
import Mathlib.Tactic.NormNum.Prime

namespace Brockian.Wheel


theorem prime_1889 : Nat.Prime 1889 := by norm_num

end Brockian.Wheel

/-
# Level-2 Goldbach wheel moduli

This file introduces the predicate `Brockian.GoldbachWheelK2` on a modulus `m`,
together with a general criterion reducing it to a bounded Goldbach verification.
Individual moduli of the family are verified in the accompanying files.
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Common
import Mathlib.Tactic.IntervalCases

namespace Brockian

/-- `GoldbachWheelK2 m` says that `m` is a *level-2 Goldbach wheel modulus*:
every residue class `r` modulo `m` is represented by a sum of two primes
`p + q` of size at most `2 * m`, i.e. the sums of two primes of size at most
twice the modulus already sweep out the whole wheel of residues mod `m`. -/
