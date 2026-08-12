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
def GoldbachWheelK2 (m : ℕ) : Prop :=
  ∀ r : ZMod m, ∀ N : ℕ, ∃ p q : ℕ,
    N < p ∧ p < q ∧ Nat.Prime p ∧ Nat.Prime q ∧ ((p : ZMod m) + (q : ZMod m) = r)

/-- In `ZMod m` for `m` an odd prime, every element `r` can be split as `a + (r - a)` with
both summands nonzero: take `a = 1` unless `r = 1`, in which case take `a = 2`. -/
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
theorem goldbachWheelK2_of_prime_ne_two {m : ℕ} (hm : Nat.Prime m) (hm2 : m ≠ 2) :
    GoldbachWheelK2 m := by
  haveI : Fact (Nat.Prime m) := ⟨hm⟩
  haveI : NeZero m := ⟨hm.ne_zero⟩
  intro r N
  obtain ⟨a, ha, hra⟩ := exists_split_ne_zero hm2 r
  have hau : IsUnit a := isUnit_iff_ne_zero.2 ha
  have hbu : IsUnit (r - a) := isUnit_iff_ne_zero.2 hra
  obtain ⟨p, hpN, hp, hpa⟩ := Nat.forall_exists_prime_gt_and_eq_mod hau N
  obtain ⟨q, hqp, hq, hqb⟩ := Nat.forall_exists_prime_gt_and_eq_mod hbu p
  exact ⟨p, q, hpN, hqp, hp, hq, by rw [hpa, hqb]; ring⟩

/-- The new wheel modulus `631` belongs to the `GoldbachWheelK2` family. -/
theorem GoldbachWheelK2_631 : GoldbachWheelK2 631 :=
  goldbachWheelK2_of_prime_ne_two (by norm_num) (by norm_num)

/-- The new wheel modulus `1009` belongs to the `GoldbachWheelK2` family. -/
theorem GoldbachWheelK2_1009 : GoldbachWheelK2 1009 :=
  goldbachWheelK2_of_prime_ne_two (by norm_num) (by norm_num)

/-- The new wheel modulus `2003` belongs to the `GoldbachWheelK2` family. -/
theorem GoldbachWheelK2_2003 : GoldbachWheelK2 2003 :=
  goldbachWheelK2_of_prime_ne_two (by norm_num) (by norm_num)

/-- The wheel condition is not vacuous: no even modulus is a Goldbach wheel modulus of
order 2, since beyond the bound `N = 2` all the primes involved are odd, so `p + q` is
always even modulo `m`. -/
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

