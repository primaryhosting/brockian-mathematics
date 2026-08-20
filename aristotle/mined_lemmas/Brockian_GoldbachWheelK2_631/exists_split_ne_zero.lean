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

theorem exists_split_ne_zero {m : ℕ} [Fact (Nat.Prime m)] (hm2 : m ≠ 2) (r : ZMod m) :
    ∃ a : ZMod m, a ≠ 0 ∧ r - a ≠ 0 := by
  have hm1 : (1 : ZMod m) ≠ 0 := one_ne_zero
  have hm2' : (2 : ZMod m) ≠ 0 := by
    intro h
    have h2 : ((2 : ℕ) : ZMod m) = 0 := by exact_mod_cast h
    have hdvd : m ∣ 2 := (ZMod.natCast_eq_zero_iff 2 m).mp h2
    exact hm2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime m) Nat.prime_two).1 hdvd)
  by_cases hr : r = 1
  · subst hr
    exact ⟨2, hm2', fun h => hm1 (by linear_combination -h)⟩
  · exact ⟨1, hm1, fun h => hr (by linear_combination h)⟩

/-- **Every odd prime modulus is a Goldbach wheel modulus of order 2.**
The proof splits a residue `r` as a sum of two units of the field `ZMod m` and then uses
Dirichlet's theorem on primes in arithmetic progressions to realize each unit by an
arbitrarily large prime. -/
