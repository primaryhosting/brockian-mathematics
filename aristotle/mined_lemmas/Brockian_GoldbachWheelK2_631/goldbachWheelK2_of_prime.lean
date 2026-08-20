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
