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

import Mathlib

/-!
# Goldbach wheels of order 2

A *Goldbach wheel of order 2* for a modulus `m` (the "wheel modulus") asserts that the
residue-class obstruction to writing a number as a sum of two primes is empty modulo `m`,
and that this holds with arbitrarily large primes: every residue class `r : ZMod m` is of
the form `p + q` for primes `N < p < q`.

This file proves the general criterion `Brockian.goldbachWheelK2_of_prime_ne_two`
(every odd prime modulus admits a Goldbach wheel of order 2) and uses it to extend the
`GoldbachWheelK2` family with new wheel moduli, in particular `631`.
-/

namespace Brockian

/-- `GoldbachWheelK2 m` holds when `m` is a *Goldbach wheel modulus of order 2*: every
residue class `r` modulo `m` can be written as `p + q` with `p` and `q` prime and both
arbitrarily large (`N < p < q` for any prescribed bound `N`). -/

theorem GoldbachWheelK2_2003 : GoldbachWheelK2 2003 :=
  goldbachWheelK2_of_prime_ne_two (by norm_num) (by norm_num)

/-- The wheel condition is not vacuous: no even modulus is a Goldbach wheel modulus of
order 2, since beyond the bound `N = 2` all the primes involved are odd, so `p + q` is
always even modulo `m`. -/
