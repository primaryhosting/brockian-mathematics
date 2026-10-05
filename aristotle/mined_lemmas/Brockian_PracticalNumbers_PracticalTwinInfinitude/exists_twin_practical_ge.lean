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
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

A natural number `n` is *practical* if every `m ≤ n` is a sum of distinct divisors of `n`.
We prove that there are infinitely many `n` such that `n` and `n + 2` are both practical.

The proof is completely explicit.  Two families of practical numbers are established by
direct subset-sum arguments:

* `2 ^ k * u` is practical whenever `u` is odd and `u ≤ 2 ^ (k+1)`;
* `2 * 3 ^ b * t` is practical whenever `t` is odd, prime to `3`, and `t ≤ 3 ^ b`.

Given `b ≥ 1`, put `s = Nat.log 2 (3 ^ b)`, so `2 ^ s ≤ 3 ^ b < 2 ^ (s+1)`, and let `M` be the
Chinese-remainder solution of `M ≡ 0 [MOD 3 ^ b]`, `M ≡ -1 [MOD 2 ^ s]` with `M < 3 ^ b * 2 ^ s`.
Then `2 * M` lies in the second family and `2 * M + 2 = 2 * (M + 1)` lies in the first, so
`(2 * M, 2 * M + 2)` is a twin pair of practical numbers of size at least `2 * 3 ^ b`.
-/

namespace Brockian.PracticalNumbers

open Finset

/-- A positive integer `n` is *practical* if every `m ≤ n` can be written as a sum of
distinct divisors of `n`. -/

lemma exists_twin_practical_ge (b : ℕ) (hb : 1 ≤ b) :
    ∃ n : ℕ, 2 * 3 ^ b ≤ n ∧ Practical n ∧ Practical (n + 2) := by
  -- the two moduli
  have hP3 : 3 ≤ 3 ^ b := by
    calc (3 : ℕ) = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  have hPne : (3 : ℕ) ^ b ≠ 0 := by positivity
  set s := Nat.log 2 (3 ^ b) with hsdef
  have h2s : 2 ^ s ≤ 3 ^ b := Nat.pow_log_le_self 2 hPne
  have hPlt : (3 : ℕ) ^ b < 2 ^ (s + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hs1 : 1 ≤ s := Nat.log_pos (by norm_num) (by omega)
  have h2spos : 0 < (2 : ℕ) ^ s := Nat.pow_pos (by norm_num) s
  have hcop : Nat.Coprime (3 ^ b) (2 ^ s) := Nat.Coprime.pow (by norm_num)
  -- Chinese remainder
  obtain ⟨M, hM0, hM1⟩ := Nat.chineseRemainder hcop 0 (2 ^ s - 1)
  have hMlt : M < 3 ^ b * 2 ^ s :=
    Nat.chineseRemainder_lt_mul hcop 0 (2 ^ s - 1) hPne (by omega)
  have hdvd3 : (3 : ℕ) ^ b ∣ M := (Nat.modEq_zero_iff_dvd).mp hM0
  have hdvd2 : (2 : ℕ) ^ s ∣ M + 1 := by
    have h : M % 2 ^ s = (2 ^ s - 1) % 2 ^ s := hM1
    rw [Nat.mod_eq_of_lt (by omega)] at h
    have h2 : (M + 1) % 2 ^ s = ((M % 2 ^ s) + 1 % 2 ^ s) % 2 ^ s := Nat.add_mod M 1 (2 ^ s)
    rw [h, Nat.mod_eq_of_lt (by omega)] at h2
    have h3 : 2 ^ s - 1 + 1 = 2 ^ s := by omega
    rw [h3, Nat.mod_self] at h2
    exact (Nat.dvd_iff_mod_eq_zero _ _).mpr h2
  have hMpos : 0 < M := by
    rcases Nat.eq_zero_or_pos M with rfl | h
    · have : (2 : ℕ) ^ s ∣ 1 := by simpa using hdvd2
      have := Nat.le_of_dvd (by norm_num) this
      have : (2 : ℕ) ≤ 2 ^ s := by
        calc (2 : ℕ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs1
      omega
    · exact h
  have hModd : Odd M := by
    have h2 : (2 : ℕ) ∣ M + 1 := dvd_trans (dvd_pow_self 2 (by omega)) hdvd2
    rcases Nat.even_or_odd M with he | ho
    · exfalso
      rw [Nat.even_iff] at he
      omega
    · exact ho
  refine ⟨2 * M, ?_, ?_, ?_⟩
  · have := Nat.le_of_dvd hMpos hdvd3
    omega
  · -- `2 * M` is practical
    obtain ⟨e, t, hMe, ht3⟩ := exists_factor_pow (p := 3) (by norm_num) M hMpos
    have hbe : b ≤ e := le_of_pow_dvd (by norm_num) ht3 (hMe ▸ hdvd3)
    have h3b3e : (3 : ℕ) ^ b ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) hbe
    have htodd : Odd t := by
      rcases Nat.even_or_odd t with he' | ho
      · exfalso
        obtain ⟨r, hr⟩ := he'
        rw [Nat.odd_iff] at hModd
        rw [hMe, hr] at hModd
        omega
      · exact ho
    have htlt : t < 2 ^ s := by
      by_contra hcon
      push_neg at hcon
      have : (3 : ℕ) ^ e * 2 ^ s ≤ 3 ^ e * t := Nat.mul_le_mul_left _ hcon
      have h2 : (3 : ℕ) ^ b * 2 ^ s ≤ 3 ^ e * 2 ^ s := Nat.mul_le_mul_right _ h3b3e
      omega
    have htle : t ≤ 3 ^ e := by omega
    have hrw : 2 * M = 2 * 3 ^ e * t := by rw [hMe]; ring
    rw [hrw]
    exact practical_two_three_pow_mul htodd ht3 htle
  · -- `2 * M + 2 = 2 * (M + 1)` is practical
    have hK : 2 * M + 2 = 2 * (M + 1) := by ring
    have hKpos : 0 < 2 * (M + 1) := by omega
    obtain ⟨k, u, hKe, hu2⟩ := exists_factor_pow (p := 2) (by norm_num) (2 * (M + 1)) hKpos
    have hdvdK : (2 : ℕ) ^ (s + 1) ∣ 2 * (M + 1) := by
      rw [pow_succ, mul_comm ((2:ℕ)^s) 2]
      exact Nat.mul_dvd_mul_left 2 hdvd2
    have hsk : s + 1 ≤ k := le_of_pow_dvd (by norm_num) hu2 (hKe ▸ hdvdK)
    have huodd : Odd u := by
      rcases Nat.even_or_odd u with he' | ho
      · exact absurd he'.two_dvd hu2
      · exact ho
    have hule : u ≤ 2 ^ (k + 1) := by
      -- `2 ^ k * u = 2 * (M+1) ≤ 2 * 3 ^ b * 2 ^ s < 2 ^ (s+1) * 2 ^ (s+1) ≤ 2 ^ k * 2 ^ (s+1)`
      have h1 : (2 : ℕ) ^ k * u < 2 ^ (s + 1) * 2 ^ (s + 1) := by
        have hb1 : M + 1 ≤ 3 ^ b * 2 ^ s := by omega
        calc (2 : ℕ) ^ k * u = 2 * (M + 1) := hKe.symm
          _ ≤ 2 * (3 ^ b * 2 ^ s) := by omega
          _ < 2 * (2 ^ (s + 1) * 2 ^ s) := by
              have : (3 : ℕ) ^ b * 2 ^ s < 2 ^ (s + 1) * 2 ^ s :=
                (Nat.mul_lt_mul_right h2spos).mpr hPlt
              omega
          _ = 2 ^ (s + 1) * 2 ^ (s + 1) := by ring
      have h2 : (2 : ℕ) ^ (s + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hsk
      have h3 : (2 : ℕ) ^ k * u < 2 ^ k * 2 ^ (s + 1) := by
        calc (2 : ℕ) ^ k * u < 2 ^ (s + 1) * 2 ^ (s + 1) := h1
          _ ≤ 2 ^ k * 2 ^ (s + 1) := Nat.mul_le_mul_right _ h2
      have h4 : u < 2 ^ (s + 1) :=
        lt_of_mul_lt_mul_left h3 (Nat.zero_le _)
      have h5 : (2 : ℕ) ^ k ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [hK, hKe]
    exact practical_two_pow_mul_odd huodd hule

/-- **Practical twin infinitude**: there are infinitely many `n` such that both `n` and
`n + 2` are practical numbers. -/
