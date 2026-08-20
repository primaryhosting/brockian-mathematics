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

theorem GoldbachWheelK2_1009 : GoldbachWheelK2 1009 :=
  goldbachWheelK2_of_prime (by norm_num) (by norm_num)

end Brockian

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

