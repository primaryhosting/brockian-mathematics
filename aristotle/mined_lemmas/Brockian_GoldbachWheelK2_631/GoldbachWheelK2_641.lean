import Mathlib

/-!
# Goldbach wheel conditions of order 2

For a *wheel modulus* `m`, the order-2 Goldbach wheel condition `GoldbachWheelK2 m`
says that every residue class `e : ZMod m` is hit by a sum `p + q` of two primes,
both coprime to `m` (i.e. both lying on the wheel of `m`), and with `p, q` arbitrarily
large.  This is the residue-class ("wheel") shadow of the Goldbach property: no
congruence obstruction mod `m` can prevent an integer from being a sum of two
wheel primes.

The main general result is `Brockian.goldbachWheelK2_of_prime`, which establishes the
condition for every odd prime modulus, and the family members
`Brockian.GoldbachWheelK2_631`, `Brockian.GoldbachWheelK2_641`,
`Brockian.GoldbachWheelK2_1009` are instances of it.
-/

namespace Brockian

/-- The order-2 Goldbach wheel condition at modulus `m`: every residue class mod `m`
is the class of a sum of two arbitrarily large primes, each coprime to `m`. -/

theorem GoldbachWheelK2_641 : GoldbachWheelK2 641 :=
  goldbachWheelK2_of_prime (by norm_num) (by norm_num)

/-- The wheel modulus `1009` (a prime) satisfies the order-2 Goldbach wheel condition. -/
