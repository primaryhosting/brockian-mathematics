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
def IsSophieGermainPrime (p : ℕ) : Prop := p.Prime ∧ (2 * p + 1).Prime

/-- The set of Sophie Germain primes. -/
def sophieGermainSet : Set ℕ := {p | IsSophieGermainPrime p}

/-- The "Mersenne-type divisibility" reformulation: primes `p` such that `2 * p + 1`
divides `2 ^ p - 1` or `2 ^ p + 1`. -/
def divisibilitySet : Set ℕ := {p | p.Prime ∧ ((2 * p + 1) ∣ 2 ^ p - 1 ∨ (2 * p + 1) ∣ 2 ^ p + 1)}

section Auxiliary

/-- A prime divisor of `2 * p + 1` is different from `2`, hence `2` is invertible mod it. -/
lemma two_ne_zero_of_dvd {p r : ℕ} (hr : r.Prime) (hrq : r ∣ 2 * p + 1) :
    (2 : ZMod r) ≠ 0 := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by
    rintro rfl
    omega
  intro h
  have hc : ((2 : ℕ) : ZMod r) = 0 := by push_cast; exact h
  have hdvd : r ∣ 2 := (ZMod.natCast_eq_zero_iff 2 r).mp hc
  have := Nat.le_of_dvd (by norm_num) hdvd
  have := hr.two_le
  omega

/-- If a prime `r` divides `2 * p + 1` and the order of `2` modulo `r` is `p`,
then `r = 2 * p + 1`. -/
lemma eq_of_orderOf_eq {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hrq : r ∣ 2 * p + 1)
    (hord : orderOf (2 : ZMod r) = p) : r = 2 * p + 1 := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hdvd : p ∣ r - 1 := by
    have h1 := ZMod.pow_card_sub_one_eq_one (two_ne_zero_of_dvd (p := p) hr hrq)
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rwa [hord] at h2
  have hle : r ≤ 2 * p + 1 := Nat.le_of_dvd (by omega) hrq
  have hr2 : 2 ≤ r := hr.two_le
  obtain ⟨k, hk⟩ := hdvd
  have hp2 : 2 ≤ p := hp.two_le
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · omega
    · omega
  have hk' : r = p * k + 1 := by omega
  have hk2 : k ≤ 2 := by
    have hmul : p * k ≤ p * 2 := by omega
    exact Nat.le_of_mul_le_mul_left hmul (by omega)
  interval_cases k
  · -- `r = p + 1` : then `p + 1` divides both `2 * p + 2` and `2 * p + 1`, hence divides `1`.
    exfalso
    have h1 : r ∣ 2 * p + 2 := ⟨2, by omega⟩
    have h2 : r ∣ 1 := by
      have := Nat.dvd_sub h1 hrq
      simpa using this
    have := Nat.le_of_dvd one_pos h2
    omega
  · omega

/-- The order of `2` modulo a prime `r` is never `1`. -/
lemma orderOf_two_ne_one {r : ℕ} (hr : r.Prime) : orderOf (2 : ZMod r) ≠ 1 := by
  haveI : Fact r.Prime := ⟨hr⟩
  intro h
  have h2 : (2 : ZMod r) = 1 := orderOf_eq_one_iff.mp h
  have hc : ((1 : ℕ) : ZMod r) = 0 := by push_cast; linear_combination h2
  have hdvd : r ∣ 1 := (ZMod.natCast_eq_zero_iff 1 r).mp hc
  have := Nat.le_of_dvd one_pos hdvd
  have := hr.two_le
  omega

/-- If `d` divides `2 * p` with `p` prime but `d` does not divide `p`, then `d = 2` or `d = 2 * p`. -/
lemma dvd_two_mul_prime {p d : ℕ} (hp : p.Prime) (hd : d ∣ 2 * p) (hnd : ¬ d ∣ p) :
    d = 2 ∨ d = 2 * p := by
  have hpos : 0 < p := hp.pos
  by_cases hpd : p ∣ d
  · right
    obtain ⟨t, rfl⟩ := hpd
    have hd' : p * t ∣ p * 2 := by rwa [mul_comm 2 p] at hd
    have ht : t ∣ 2 := (Nat.mul_dvd_mul_iff_left hpos).mp hd'
    have ht2 : t ≤ 2 := Nat.le_of_dvd (by norm_num) ht
    interval_cases t
    · simp only [Nat.mul_zero, Nat.zero_dvd] at hd; omega
    · simp at hnd
    · exact mul_comm p 2
  · left
    have hcop : Nat.Coprime d p := Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd)
    have hd2 : d ∣ 2 := hcop.dvd_of_dvd_mul_right hd
    have h2 : d ≤ 2 := Nat.le_of_dvd (by norm_num) hd2
    interval_cases d
    · simp only [Nat.zero_dvd] at hd; omega
    · exact absurd (one_dvd p) hnd
    · rfl

/-- `2 ^ n` is periodic modulo `9` with period `6`. -/
lemma two_pow_mod_nine (n : ℕ) : 2 ^ n % 9 = 2 ^ (n % 6) % 9 := by
  conv_lhs => rw [← Nat.div_add_mod n 6]
  rw [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

end Auxiliary

/-- **Criterion, minus case.** If `p` is prime and `2 * p + 1` divides `2 ^ p - 1`,
then `2 * p + 1` is prime. -/
theorem prime_of_dvd_two_pow_sub_one {p : ℕ} (hp : p.Prime) (h : (2 * p + 1) ∣ 2 ^ p - 1) :
    (2 * p + 1).Prime := by
  have hp2 : 2 ≤ p := hp.two_le
  have key : ∀ r : ℕ, r.Prime → r ∣ 2 * p + 1 → r = 2 * p + 1 := by
    intro r hr hrq
    haveI : Fact r.Prime := ⟨hr⟩
    have hrd : r ∣ 2 ^ p - 1 := hrq.trans h
    have hcast : ((2 ^ p - 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ r).mpr hrd
    have hone : (1 : ℕ) ≤ 2 ^ p := Nat.one_le_two_pow
    rw [Nat.cast_sub hone] at hcast
    push_cast at hcast
    have hpow : (2 : ZMod r) ^ p = 1 := sub_eq_zero.mp hcast
    have hord : orderOf (2 : ZMod r) ∣ p := orderOf_dvd_of_pow_eq_one hpow
    rcases hp.eq_one_or_self_of_dvd _ hord with h1 | h1
    · exact absurd h1 (orderOf_two_ne_one hr)
    · exact eq_of_orderOf_eq hp hr hrq h1
  rw [Nat.prime_def_minFac]
  exact ⟨by omega, key _ (Nat.minFac_prime (by omega)) (Nat.minFac_dvd _)⟩

/-- **Criterion, plus case.** If `p` is prime and `2 * p + 1` divides `2 ^ p + 1`,
then `2 * p + 1` is prime. -/
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
theorem dvd_of_sophieGermain {p : ℕ} (hp : p.Prime) (hq : (2 * p + 1).Prime) :
    (2 * p + 1) ∣ 2 ^ p - 1 ∨ (2 * p + 1) ∣ 2 ^ p + 1 := by
  set q := 2 * p + 1 with hqdef
  haveI : Fact q.Prime := ⟨hq⟩
  have hp2 : 2 ≤ p := hp.two_le
  have hne : (2 : ZMod q) ≠ 0 := by
    intro hcon
    have hc : ((2 : ℕ) : ZMod q) = 0 := by push_cast; exact hcon
    have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 2 q).mp hc)
    omega
  have h1 : (2 : ZMod q) ^ (q - 1) = 1 := ZMod.pow_card_sub_one_eq_one hne
  have h2 : ((2 : ZMod q) ^ p) * ((2 : ZMod q) ^ p) = 1 := by
    rw [← pow_add]
    have hpp : p + p = q - 1 := by omega
    rw [hpp]; exact h1
  rcases mul_self_eq_one_iff.mp h2 with h3 | h3
  · left
    have hz : ((2 ^ p - 1 : ℕ) : ZMod q) = 0 := by
      rw [Nat.cast_sub Nat.one_le_two_pow]
      push_cast
      rw [h3]; ring
    exact (ZMod.natCast_eq_zero_iff _ q).mp hz
  · right
    have hz : ((2 ^ p + 1 : ℕ) : ZMod q) = 0 := by
      push_cast
      rw [h3]; ring
    exact (ZMod.natCast_eq_zero_iff _ q).mp hz

/-- The divisibility reformulation describes exactly the Sophie Germain primes. -/
theorem divisibilitySet_eq_sophieGermainSet : divisibilitySet = sophieGermainSet := by
  ext p
  constructor
  · rintro ⟨hp, hd | hd⟩
    · exact ⟨hp, prime_of_dvd_two_pow_sub_one hp hd⟩
    · exact ⟨hp, prime_of_dvd_two_pow_add_one hp hd⟩
  · rintro ⟨hp, hq⟩
    exact ⟨hp, dvd_of_sophieGermain hp hq⟩

/-- Small Sophie Germain primes, verified by decision procedure. -/
theorem sophieGermain_examples :
    ∀ p ∈ [2, 3, 5, 11, 23, 29, 41, 53, 83, 89], IsSophieGermainPrime p := by
  intro p hp
  fin_cases hp <;> exact ⟨by norm_num, by norm_num⟩

/-- **Conditional reduction of the Sophie Germain conjecture.**
If there are arbitrarily large primes `p` for which `2 * p + 1` divides `2 ^ p - 1` or
`2 ^ p + 1`, then there are infinitely many Sophie Germain primes. -/
theorem SophieGermainInfinitude
    (h : ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ ((2 * p + 1) ∣ 2 ^ p - 1 ∨ (2 * p + 1) ∣ 2 ^ p + 1)) :
    {p : ℕ | p.Prime ∧ (2 * p + 1).Prime}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨p, hN, hp, hd⟩ := h N
  refine ⟨p, ?_, hN⟩
  rcases hd with hd | hd
  · exact ⟨hp, prime_of_dvd_two_pow_sub_one hp hd⟩
  · exact ⟨hp, prime_of_dvd_two_pow_add_one hp hd⟩

/-- The hypothesis of `SophieGermainInfinitude` is *equivalent* to the Sophie Germain
conjecture, so the reduction loses nothing. -/
theorem sophieGermainInfinitude_iff :
    (∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ ((2 * p + 1) ∣ 2 ^ p - 1 ∨ (2 * p + 1) ∣ 2 ^ p + 1)) ↔
      {p : ℕ | p.Prime ∧ (2 * p + 1).Prime}.Infinite := by
  constructor
  · exact SophieGermainInfinitude
  · intro hinf N
    obtain ⟨p, hp, hN⟩ := hinf.exists_gt N
    exact ⟨p, hN, hp.1, dvd_of_sophieGermain hp.1 hp.2⟩

end Brockian.SophieGermain

