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
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace Brockian.CullenWoodall

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction; `W 0 = 0`). -/

theorem exists_dvd_woodall {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    ∃ n, 1 ≤ n ∧ p ∣ woodall n := by
  have hp2 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hodd)
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hodd)
  have hcop : Nat.Coprime (p - 1) p := by
    have h1 : Nat.Coprime (p - 1) ((p - 1) + 1) := by simp
    rwa [show (p - 1) + 1 = p by omega] at h1
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop 1 ((p + 1) / 2)
  -- `k ≡ 1 [MOD p-1]` and `k ≡ (p+1)/2 [MOD p]`
  have hmod : k % p = (p + 1) / 2 := by
    have hlt : (p + 1) / 2 < p := by omega
    have := hk2
    rwa [Nat.ModEq, Nat.mod_eq_of_lt hlt] at this
  have hkpos : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · simp at hmod; omega
    · exact h
  have hkmod : k % (p - 1) = 1 := by
    have := hk1
    rwa [Nat.ModEq, Nat.mod_eq_of_lt (by omega : 1 < p - 1)] at this
  obtain ⟨t, ht⟩ : ∃ t, k = (p - 1) * t + 1 := by
    refine ⟨k / (p - 1), ?_⟩
    have := Nat.div_add_mod k (p - 1)
    omega
  have hcop2 : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hodd)
  have hferm : (2:ℕ) ^ (p - 1) ≡ 1 [MOD p] := by
    have := Nat.ModEq.pow_totient hcop2
    rwa [Nat.totient_prime hp] at this
  have hpow : (2:ℕ) ^ k ≡ 2 [MOD p] := by
    calc (2:ℕ) ^ k = ((2 ^ (p - 1)) ^ t) * 2 := by rw [← pow_mul, ← pow_succ, ← ht]
      _ ≡ (1 ^ t) * 2 [MOD p] := Nat.ModEq.mul_right 2 (hferm.pow t)
      _ = 2 := by ring
  have hfinal : k * 2 ^ k ≡ 1 [MOD p] := by
    have h1 : k * 2 ^ k ≡ ((p + 1) / 2) * 2 [MOD p] := hk2.mul hpow
    have h2 : ((p + 1) / 2) * 2 = p + 1 := by omega
    have h3 : p + 1 ≡ 0 + 1 [MOD p] := Nat.ModEq.add_right 1 (Nat.modEq_zero_iff_dvd.mpr dvd_rfl)
    rw [h2] at h1
    simpa using h1.trans h3
  exact ⟨k, hkpos, (dvd_woodall_iff hkpos).mpr hfinal⟩

/-- For every odd prime `p` there are infinitely many `n` with `p ∣ W n`. -/
