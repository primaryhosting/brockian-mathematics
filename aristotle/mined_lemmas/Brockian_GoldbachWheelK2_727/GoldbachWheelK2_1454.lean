import Mathlib

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Brockian

/-- The *Goldbach wheel condition of order 2* for a modulus `m`:
every even number `n` is congruent, modulo `m`, to a sum `a + b` of two natural numbers
that are both coprime to `m`.

This is the condition saying that the "wheel" of modulus `m` does not obstruct
Goldbach-type representations of even numbers as sums of two numbers coprime to `m`
(in particular, as sums of two primes not dividing `m`). -/

theorem GoldbachWheelK2_1454 : GoldbachWheelK2 1454 := goldbachWheelK2_of_pos (by norm_num)

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

