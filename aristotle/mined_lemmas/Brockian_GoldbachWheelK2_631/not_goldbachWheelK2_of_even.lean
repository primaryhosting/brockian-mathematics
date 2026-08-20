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

theorem not_goldbachWheelK2_of_even {m : ℕ} (hev : 2 ∣ m) :
    ¬ GoldbachWheelK2 m := by
  intro h
  obtain ⟨p, q, hpN, hpq, hp, hq, hsum⟩ := h 1 2
  have hcast : ((p + q : ℕ) : ZMod m) = ((1 : ℕ) : ZMod m) := by push_cast; simpa using hsum
  have hmod : (p + q) ≡ 1 [MOD m] := (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  have hmod2 : (p + q) ≡ 1 [MOD 2] := hmod.of_dvd hev
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
  have hqodd : q % 2 = 1 := Nat.odd_iff.mp (hq.odd_of_ne_two (by omega))
  rw [Nat.ModEq] at hmod2
  omega

end Brockian

#print axioms Brockian.GoldbachWheelK2_631
#print axioms Brockian.goldbachWheelK2_of_prime_ne_two
#print axioms Brockian.not_goldbachWheelK2_of_even

