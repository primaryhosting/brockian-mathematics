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
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.SophieGermain

/-- `p` is a Sophie Germain prime if both `p` and `2 * p + 1` are prime. -/

theorem prime_of_dvd_two_pow_add_one {p : ℕ} (hp : p.Prime) (h : (2 * p + 1) ∣ 2 ^ p + 1) :
    (2 * p + 1).Prime := by
  have hp2 : 2 ≤ p := hp.two_le
  -- Every prime divisor of `2 * p + 1` is either `3` or `2 * p + 1` itself.
  have key : ∀ r : ℕ, r.Prime → r ∣ 2 * p + 1 → r = 3 ∨ r = 2 * p + 1 := by
    intro r hr hrq
    haveI : Fact r.Prime := ⟨hr⟩
    have hrd : r ∣ 2 ^ p + 1 := hrq.trans h
    have hcast : ((2 ^ p + 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ r).mpr hrd
    push_cast at hcast
    have hneg : (2 : ZMod r) ^ p = -1 := by linear_combination hcast
    have hsq : (2 : ZMod r) ^ (2 * p) = 1 := by rw [two_mul, pow_add, hneg]; ring
    have hdord : orderOf (2 : ZMod r) ∣ 2 * p := orderOf_dvd_of_pow_eq_one hsq
    have hnd : ¬ orderOf (2 : ZMod r) ∣ p := by
      intro hcon
      have h1 : (2 : ZMod r) ^ p = 1 := orderOf_dvd_iff_pow_eq_one.mp hcon
      rw [hneg] at h1
      exact two_ne_zero_of_dvd hr hrq (by linear_combination -h1)
    rcases dvd_two_mul_prime hp hdord hnd with hd2 | hd2p
    · -- the order is `2`, so `r` divides `3`
      left
      have h4 : (2 : ZMod r) ^ 2 = 1 := by rw [← hd2]; exact pow_orderOf_eq_one _
      have hc3 : ((3 : ℕ) : ZMod r) = 0 := by push_cast; linear_combination h4
      exact (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp ((ZMod.natCast_eq_zero_iff 3 r).mp hc3)
    · -- the order is `2 * p`, so `2 * p ∣ r - 1` forces `r = 2 * p + 1`
      right
      have hfer : (2 : ZMod r) ^ (r - 1) = 1 :=
        ZMod.pow_card_sub_one_eq_one (two_ne_zero_of_dvd hr hrq)
      have hdd : orderOf (2 : ZMod r) ∣ r - 1 := orderOf_dvd_of_pow_eq_one hfer
      rw [hd2p] at hdd
      have hle : r ≤ 2 * p + 1 := Nat.le_of_dvd (by omega) hrq
      have hr2 := hr.two_le
      have := Nat.le_of_dvd (by omega) hdd
      omega
  by_contra hnp
  -- otherwise `2 * p + 1` would be a power of `3`, in particular divisible by `9`
  have hm : (2 * p + 1).minFac ≠ 2 * p + 1 := fun hh =>
    hnp (Nat.prime_def_minFac.mpr ⟨by omega, hh⟩)
  have hmp : ((2 * p + 1).minFac).Prime := Nat.minFac_prime (by omega)
  have h3 : (2 * p + 1).minFac = 3 := (key _ hmp (Nat.minFac_dvd _)).resolve_right hm
  have h3dvd : (3 : ℕ) ∣ 2 * p + 1 := h3 ▸ Nat.minFac_dvd _
  obtain ⟨m, hm3⟩ := h3dvd
  have hm1 : 1 < m := by omega
  have hmpf : (m.minFac).Prime := Nat.minFac_prime (by omega)
  have hdvdq : m.minFac ∣ 2 * p + 1 := (Nat.minFac_dvd m).trans ⟨3, by omega⟩
  have hlt : m.minFac ≤ m := Nat.minFac_le (by omega)
  have hne : m.minFac ≠ 2 * p + 1 := by omega
  have hmf3 : m.minFac = 3 := (key _ hmpf hdvdq).resolve_right hne
  have h9 : (9 : ℕ) ∣ 2 * p + 1 := by
    obtain ⟨u, hu⟩ := Nat.minFac_dvd m
    rw [hmf3] at hu
    exact ⟨u, by omega⟩
  have h9d : (9 : ℕ) ∣ 2 ^ p + 1 := h9.trans h
  have hmod : 2 ^ p % 9 = 8 := by omega
  have hcyc : 2 ^ p % 9 = 2 ^ (p % 6) % 9 := two_pow_mod_nine p
  rw [hmod] at hcyc
  have hs : p % 6 < 6 := Nat.mod_lt _ (by norm_num)
  have hp6 : p % 6 = 3 := by interval_cases hx : (p % 6) <;> omega
  have hp3 : (3 : ℕ) ∣ p := by omega
  have hpeq : p = 3 := ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp hp3).symm
  subst hpeq
  omega

/-- **Easy direction.** If `p` and `2 * p + 1` are both prime, then `2 * p + 1` divides
`2 ^ p - 1` or `2 ^ p + 1`. -/
