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
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Whether there are infinitely many amicable numbers is an open problem.  What is proved here
is an unconditional formalisation of Thabit ibn Qurra's rule together with the resulting
*conditional reduction*: if there are infinitely many Thabit indices `k` (i.e. indices for
which `3·2^(k-1) - 1`, `3·2^k - 1` and `9·2^(2k-1) - 1` are all prime), then there are
infinitely many amicable numbers.
-/

namespace Brockian.AmicableNumbers

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- The sum of the proper divisors of `n` (the classical `s`-function). -/

theorem thabit_isAmicablePair {k p q r : ℕ} (hk : 2 ≤ k)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r)
    (hp' : p + 1 = 3 * 2 ^ (k - 1)) (hq' : q + 1 = 3 * 2 ^ k)
    (hr' : r + 1 = 9 * 2 ^ (2 * k - 1)) :
    IsAmicablePair (2 ^ k * p * q) (2 ^ k * r) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rw [show j + 2 - 1 = j + 1 from rfl] at hp'
  rw [show 2 * (j + 2) - 1 = 2 * j + 3 by omega] at hr'
  -- parities
  have hp2 : p % 2 = 1 := by rw [pow_succ] at hp'; omega
  have hq2 : q % 2 = 1 := by rw [pow_succ] at hq'; omega
  have hr2 : r % 2 = 1 := by rw [pow_succ] at hr'; omega
  have hcop2p : Nat.Coprime 2 p := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
  have hcop2q : Nat.Coprime 2 q := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
  have hcop2r : Nat.Coprime 2 r := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
  have hlt : (2:ℕ) ^ (j + 1) < 2 ^ (j + 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hpq : p ≠ q := by omega
  have hcoppq : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  -- the two σ-values
  have hM : σ 1 (2 ^ (j + 2) * p * q) = (2 ^ (j + 3) - 1) * ((p + 1) * (q + 1)) := by
    have hcop : Nat.Coprime (2 ^ (j + 2)) (p * q) :=
      Nat.Coprime.mul_right (Nat.Coprime.pow_left _ hcop2p) (Nat.Coprime.pow_left _ hcop2q)
    rw [mul_assoc, isMultiplicative_sigma.map_mul_of_coprime hcop,
      isMultiplicative_sigma.map_mul_of_coprime hcoppq, sigma_two_pow, sigma_prime hp,
      sigma_prime hq]
  have hN : σ 1 (2 ^ (j + 2) * r) = (2 ^ (j + 3) - 1) * (r + 1) := by
    rw [isMultiplicative_sigma.map_mul_of_coprime (Nat.Coprime.pow_left _ hcop2r),
      sigma_two_pow, sigma_prime hr]
  -- the arithmetic identities, over ℤ
  set a : ℕ := 2 ^ (j + 1) with ha
  have h2a : (2:ℕ) ^ (j + 2) = 2 * a := by rw [ha]; ring
  have h4a : (2:ℕ) ^ (j + 3) = 4 * a := by rw [ha]; ring
  have h2a2 : (2:ℕ) ^ (2 * j + 3) = 2 * a ^ 2 := by rw [ha]; ring
  have ha2 : 2 ≤ a := by
    rw [ha]
    calc (2:ℕ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [h2a] at hq' hM hN ⊢
  rw [h2a2] at hr'
  rw [h4a] at hM hN
  have hpz : (p : ℤ) = 3 * a - 1 := by omega
  have hqz : (q : ℤ) = 6 * a - 1 := by omega
  have hrz : (r : ℤ) = 18 * (a : ℤ) ^ 2 - 1 := by
    have : (r : ℤ) + 1 = 9 * (2 * (a : ℤ) ^ 2) := by exact_mod_cast hr'
    linarith
  refine isAmicablePair_of_sigma ?_ ?_ ?_ ?_ ?_
  · exact Nat.mul_pos (Nat.mul_pos (by omega) hp.pos) hq.pos
  · exact Nat.mul_pos (by omega) hr.pos
  · -- distinctness
    intro hEq
    have : p * q = r := by
      have h2a0 : 0 < 2 * a := by omega
      exact Nat.eq_of_mul_eq_mul_left h2a0 (by rw [mul_assoc] at hEq; exact hEq)
    have : (p : ℤ) * q = r := by exact_mod_cast this
    rw [hpz, hqz, hrz] at this
    nlinarith [ha2, (by exact_mod_cast ha2 : (2:ℤ) ≤ (a:ℤ))]
  · rw [hM]
    zify [show (1:ℕ) ≤ 4 * a by omega]
    rw [hpz, hqz, hrz]
    ring
  · rw [hN]
    zify [show (1:ℕ) ≤ 4 * a by omega]
    rw [hpz, hqz, hrz]
    ring

/-! ## The conditional infinitude statement -/

