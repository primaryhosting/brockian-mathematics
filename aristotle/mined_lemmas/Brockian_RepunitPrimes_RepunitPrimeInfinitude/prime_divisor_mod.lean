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
# Repunit Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.RepunitPrimes.RepunitPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Repunit Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.RepunitPrimes.RepunitPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.RepunitPrimes

/-- The `n`-th base-ten repunit `Rₙ = 1 + 10 + ⋯ + 10ⁿ⁻¹ = (10ⁿ - 1)/9`. -/

theorem prime_divisor_mod {p q : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hp2 : p ≠ 2)
    (hq : q.Prime) (hdvd : q ∣ repunit p) : q % (2 * p) = 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hppos : 0 < p := hp.pos
  have hq2 : q ≠ 2 := by
    rintro rfl; exact repunit_odd hppos hdvd
  have hr : ((repunit p : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  have h9dvd : q ∣ 9 * repunit p := hdvd.mul_left 9
  -- `q` cannot divide `10`, since `q ∣ R_p` and `9 R_p + 1 = 10 ^ p`
  have hne : ((10 : ℕ) : ZMod q) ≠ 0 := by
    intro h
    have hd : q ∣ 10 := (ZMod.natCast_eq_zero_iff _ _).mp h
    have hdp : q ∣ 10 ^ p := hd.trans (dvd_pow_self 10 hppos.ne')
    have h1 : q ∣ 1 := by
      have := Nat.dvd_sub hdp h9dvd
      rwa [show 10 ^ p - 9 * repunit p = 1 by have := nine_mul_repunit_add_one p; omega] at this
    exact Nat.Prime.one_lt hq |>.ne' (Nat.dvd_one.mp h1)
  have hq3 : q ≠ 3 := by
    rintro rfl
    have h3 : (3:ℕ) ∣ p := by
      have := repunit_mod_three p
      omega
    exact hp3 (((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp h3)).symm
  -- `10` has order exactly `p` modulo `q`
  have hten : ((10 : ℕ) : ZMod q) ^ p = 1 := by
    have h9 := nine_mul_repunit_add_one p
    have h10 : ((10 ^ p : ℕ) : ZMod q) = ((9 * repunit p + 1 : ℕ) : ZMod q) := by rw [h9]
    push_cast at h10 ⊢
    rw [h10, hr]
    ring
  have hord : orderOf ((10 : ℕ) : ZMod q) ∣ p := orderOf_dvd_of_pow_eq_one hten
  have hordp : orderOf ((10 : ℕ) : ZMod q) = p := by
    rcases hp.eq_one_or_self_of_dvd _ hord with h1 | h1
    · exfalso
      have h10 : ((10 : ℕ) : ZMod q) = 1 := orderOf_eq_one_iff.mp h1
      have h9z : ((9 : ℕ) : ZMod q) = 0 := by push_cast at h10 ⊢; linear_combination h10
      have h9 : q ∣ 9 := (ZMod.natCast_eq_zero_iff _ _).mp h9z
      have hle := Nat.le_of_dvd (by norm_num) h9
      interval_cases q <;> simp_all (config := {decide := true})
    · exact h1
  have hFermat : ((10 : ℕ) : ZMod q) ^ (q - 1) = 1 := ZMod.pow_card_sub_one_eq_one hne
  have hpq : p ∣ q - 1 := by
    have := orderOf_dvd_of_pow_eq_one hFermat
    rwa [hordp] at this
  have h2q : 2 ∣ q - 1 := by
    obtain ⟨k, hk⟩ := hq.odd_of_ne_two hq2
    omega
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
  obtain ⟨k, hk⟩ := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h2q hpq
  have hq1 : 1 ≤ q := hq.one_lt.le.trans' (by norm_num)
  have hqk : q = 2 * p * k + 1 := by omega
  rw [hqk, show 2 * p * k + 1 = 1 + 2 * p * k by ring, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (by omega)]

/-- **Conditional infinitude of repunit primes.**

If there are arbitrarily large prime indices `p` for which the repunit `R_p` has no prime
divisor `q ≡ 1 (mod 2p)` with `q² ≤ R_p` — i.e. `R_p` survives the trial division to which
its prime divisors are restricted by `prime_divisor_mod` — then there are infinitely many
repunit primes.

This is a Lean-checked reduction of the (open) Brockian conjecture on the infinitude of
repunit primes to a "no small admissible factor" hypothesis. -/
