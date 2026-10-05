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

Whether there are infinitely many amicable pairs is an open problem, so the main result here
is a Lean-checked *conditional reduction*: the infinitude of amicable numbers follows from the
infinitude of the indices at which the three Thabit numbers are simultaneously prime.
Along the way Thabit ibn Qurra's rule is proved unconditionally, together with the classical
amicable pairs `(220, 284)` and `(1184, 1210)`.
-/

set_option maxRecDepth 100000

namespace Brockian.AmicableNumbers

open Finset

/-- The sum-of-divisors function `σ₁`. -/

theorem thabit_rule {k p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpe : p + 1 = 3 * 2 ^ (k + 1)) (hqe : q + 1 = 3 * 2 ^ (k + 2))
    (hre : r + 1 = 9 * 2 ^ (2 * k + 3)) :
    IsAmicablePair (2 ^ (k + 2) * p * q) (2 ^ (k + 2) * r) := by
  set a : ℕ := 2 ^ (k + 1) with ha
  have ha1 : 2 ≤ a := Nat.one_lt_two_pow (by omega)
  have ha2 : (2:ℕ) ^ (k + 2) = 2 * a := by rw [ha, pow_succ]; ring
  have ha3 : (2:ℕ) ^ (2 * k + 3) = 2 * a ^ 2 := by rw [ha, ← pow_mul]; ring_nf
  rw [ha2] at hqe
  rw [ha3] at hre
  have hpne2 : p ≠ 2 := by omega
  have hqne2 : q ≠ 2 := by omega
  have hrne2 : r ≠ 2 := by nlinarith
  have hpq : p ≠ q := by omega
  have cop2p : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hpne2)
  have cop2q : Nat.Coprime 2 q := (Nat.coprime_primes Nat.prime_two hq).2 (Ne.symm hqne2)
  have cop2r : Nat.Coprime 2 r := (Nat.coprime_primes Nat.prime_two hr).2 (Ne.symm hrne2)
  have coppq : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  have c1 : Nat.Coprime (2 ^ (k + 2)) p := Nat.Coprime.pow_left _ cop2p
  have c2 : Nat.Coprime (2 ^ (k + 2)) q := Nat.Coprime.pow_left _ cop2q
  have c3 : Nat.Coprime (2 ^ (k + 2)) r := Nat.Coprime.pow_left _ cop2r
  have c4 : Nat.Coprime (2 ^ (k + 2) * p) q := Nat.Coprime.mul_left c2 coppq
  set A : ℕ := sigmaOne (2 ^ (k + 2)) with hAdef
  have hA : A + 1 = 4 * a := by
    have h := sigmaOne_two_pow (k + 2)
    rw [← hAdef] at h
    rw [h, ha, pow_succ, pow_succ]; ring
  have e1 : sigmaOne (2 ^ (k + 2) * p * q) = A * (p + 1) * (q + 1) := by
    rw [sigmaOne_mul_of_coprime c4, sigmaOne_mul_of_coprime c1, sigmaOne_prime hp,
      sigmaOne_prime hq]
  have e2 : sigmaOne (2 ^ (k + 2) * r) = A * (r + 1) := by
    rw [sigmaOne_mul_of_coprime c3, sigmaOne_prime hr]
  have hAz : (A : ℤ) = 4 * a - 1 := by omega
  have hpz : (p : ℤ) = 3 * a - 1 := by omega
  have hqz : (q : ℤ) = 6 * a - 1 := by omega
  have hrz : (r : ℤ) = 18 * (a : ℤ) ^ 2 - 1 := by
    have : (r : ℤ) + 1 = 9 * (2 * (a:ℤ) ^ 2) := by exact_mod_cast hre
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [ha2]
    intro hcon
    have hz : (2 * (a:ℤ)) * p * q = 2 * a * r := by exact_mod_cast hcon
    rw [hpz, hqz, hrz] at hz
    nlinarith [hz]
  · rw [e1, ha2]
    have hz : (A : ℤ) * (p + 1) * (q + 1) = 2 * a * p * q + 2 * a * r := by
      rw [hAz, hpz, hqz, hrz]; ring
    exact_mod_cast hz
  · rw [e2, ha2]
    have hz : (A : ℤ) * (r + 1) = 2 * a * p * q + 2 * a * r := by
      rw [hAz, hpz, hqz, hrz]; ring
    exact_mod_cast hz

/-- The Thabit condition at index `k`: the three Thabit numbers `3·2^(k+1) - 1`,
`3·2^(k+2) - 1` and `9·2^(2k+3) - 1` are all prime. -/
