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
def GoldbachWheelK2 (m : ℕ) : Prop :=
  ∀ (e : ZMod m) (N : ℕ), ∃ p q : ℕ,
    N < p ∧ N < q ∧ Nat.Prime p ∧ Nat.Prime q ∧
      Nat.Coprime p m ∧ Nat.Coprime q m ∧ ((p + q : ℕ) : ZMod m) = e

/-- In `ZMod m` with `3 ≤ m` there is an element `a` which is neither `0` nor a given `e`. -/
lemma exists_ne_zero_ne {m : ℕ} (hm : 3 ≤ m) (e : ZMod m) :
    ∃ a : ZMod m, a ≠ 0 ∧ a ≠ e := by
  haveI : NeZero m := ⟨by omega⟩
  have h1 : ((1 : ℕ) : ZMod m) ≠ ((0 : ℕ) : ZMod m) := by
    rw [Ne, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  have h2 : ((2 : ℕ) : ZMod m) ≠ ((0 : ℕ) : ZMod m) := by
    rw [Ne, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  have h12 : ((1 : ℕ) : ZMod m) ≠ ((2 : ℕ) : ZMod m) := by
    rw [Ne, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  push_cast at h1 h2 h12
  by_cases he : (1 : ZMod m) = e
  · exact ⟨2, h2, by rw [← he]; exact fun h => h12 h.symm⟩
  · exact ⟨1, h1, he⟩

/-- Every odd prime modulus satisfies the order-2 Goldbach wheel condition.
The proof uses Dirichlet's theorem on primes in arithmetic progressions. -/
theorem goldbachWheelK2_of_prime {m : ℕ} (hm : Nat.Prime m) (hm3 : 3 ≤ m) :
    GoldbachWheelK2 m := by
  haveI : NeZero m := ⟨by omega⟩
  haveI : Fact (Nat.Prime m) := ⟨hm⟩
  intro e N
  obtain ⟨a, ha0, hae⟩ := exists_ne_zero_ne hm3 e
  have hua : IsUnit a := isUnit_iff_ne_zero.2 ha0
  have hub : IsUnit (e - a) := by
    refine isUnit_iff_ne_zero.2 ?_
    intro h
    exact hae (by linear_combination -h)
  obtain ⟨p, hpN, hp, hpa⟩ := Nat.forall_exists_prime_gt_and_eq_mod hua N
  obtain ⟨q, hqN, hq, hqb⟩ := Nat.forall_exists_prime_gt_and_eq_mod hub N
  refine ⟨p, q, hpN, hqN, hp, hq, ?_, ?_, ?_⟩
  · exact (ZMod.isUnit_iff_coprime p m).1 (hpa ▸ hua)
  · exact (ZMod.isUnit_iff_coprime q m).1 (hqb ▸ hub)
  · push_cast
    rw [hpa, hqb]
    ring

/-- The wheel modulus `631` (a prime) satisfies the order-2 Goldbach wheel condition. -/
theorem GoldbachWheelK2_631 : GoldbachWheelK2 631 :=
  goldbachWheelK2_of_prime (by norm_num) (by norm_num)

/-- The wheel modulus `641` (a prime) satisfies the order-2 Goldbach wheel condition. -/
theorem GoldbachWheelK2_641 : GoldbachWheelK2 641 :=
  goldbachWheelK2_of_prime (by norm_num) (by norm_num)

/-- The wheel modulus `1009` (a prime) satisfies the order-2 Goldbach wheel condition. -/
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

