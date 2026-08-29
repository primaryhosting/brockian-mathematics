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

/-
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.SophieGermain

/-- `p` is a *Sophie Germain prime* if both `p` and `2 * p + 1` are prime. -/

theorem prime_of_dvd_mersenne {p : ℕ} (hp : Nat.Prime p) (hd : (2 * p + 1) ∣ 2 ^ p - 1) :
    Nat.Prime (2 * p + 1) := by
  by_contra hnp
  have hp2 := hp.two_le
  have hq0 : 0 < 2 * p + 1 := by omega
  have hsq := Nat.minFac_sq_le_self hq0 hnp
  set r := (2 * p + 1).minFac with hr
  have hq1 : 2 * p + 1 ≠ 1 := by omega
  have hrp : r.Prime := Nat.minFac_prime hq1
  haveI : Fact r.Prime := ⟨hrp⟩
  have hrd : r ∣ 2 ^ p - 1 := (Nat.minFac_dvd _).trans hd
  have h2 : ((2 : ZMod r)) ^ p = 1 := by
    have h0 : ((2 ^ p - 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hrd
    have h1 : (1 : ℕ) ≤ 2 ^ p := Nat.one_le_two_pow
    rw [Nat.cast_sub h1] at h0
    push_cast at h0
    exact sub_eq_zero.mp h0
  have hne0 : (2 : ZMod r) ≠ 0 := by
    intro h
    rw [h, zero_pow (by omega : p ≠ 0)] at h2
    exact zero_ne_one h2
  have hord : orderOf (2 : ZMod r) ∣ p := orderOf_dvd_of_pow_eq_one h2
  have hne1 : orderOf (2 : ZMod r) ≠ 1 := by
    intro h
    have h21 : (2 : ZMod r) = 1 := orderOf_eq_one_iff.1 h
    have hcast : ((2 : ℕ) : ZMod r) = ((1 : ℕ) : ZMod r) := by push_cast; exact h21
    have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).1 hcast
    have hone : r ∣ 1 := (Nat.modEq_iff_dvd' (by norm_num)).1 hmod.symm
    exact hrp.one_lt.ne' (Nat.dvd_one.mp hone)
  have hordp : orderOf (2 : ZMod r) = p := (hp.eq_one_or_self_of_dvd _ hord).resolve_left hne1
  have hdvd : p ∣ r - 1 := hordp ▸ ZMod.orderOf_dvd_card_sub_one hne0
  have hr2 : 2 ≤ r := hrp.two_le
  have hle : p ≤ r - 1 := Nat.le_of_dvd (by omega) hdvd
  have hlt : p + 1 ≤ r := by omega
  nlinarith

/-- **Mersenne criterion for safe primes.** For a prime `p ≡ 3 [MOD 4]`, the number
`2 * p + 1` is prime if and only if it divides the Mersenne number `2 ^ p - 1`. -/
