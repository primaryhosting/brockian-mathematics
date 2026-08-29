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
-/

namespace Brockian.AmicableNumbers

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- The sum of all (positive) divisors of `n`.  For `n = 0` this is `0`. -/

theorem isAmicablePair_thabit {k p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpv : p + 1 = 3 * 2 ^ (k + 1)) (hqv : q + 1 = 3 * 2 ^ (k + 2))
    (hrv : r + 1 = 9 * 2 ^ (2 * k + 3)) :
    IsAmicablePair (2 ^ (k + 2) * p * q) (2 ^ (k + 2) * r) := by
  have hodd : ∀ m j : ℕ, m + 1 = 3 * 2 ^ (j + 1) → Odd m := by
    intro m j h
    have : (2 : ℕ) ^ (j + 1) = 2 * 2 ^ j := by ring
    rw [Nat.odd_iff]; omega
  have hpo : Odd p := hodd p k hpv
  have hqo : Odd q := hodd q (k + 1) (by rw [hqv])
  have hro : Odd r := by
    have : (2 : ℕ) ^ (2 * k + 3) = 2 * 2 ^ (2 * k + 2) := by ring
    rw [Nat.odd_iff]; omega
  have hpq : p ≠ q := by
    have : (2 : ℕ) ^ (k + 1) < 2 ^ (k + 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hcpq : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have h2pq : Nat.Coprime (2 ^ (k + 2)) (p * q) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr (hpo.mul hqo))
  have h2r : Nat.Coprime (2 ^ (k + 2)) r :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hro)
  have hAsum : sumOfDivisors (2 ^ (k + 2) * p * q)
      = sumOfDivisors (2 ^ (k + 2)) * ((p + 1) * (q + 1)) := by
    rw [mul_assoc, sumOfDivisors_mul_of_coprime h2pq, sumOfDivisors_mul_of_coprime hcpq,
      sumOfDivisors_prime hp, sumOfDivisors_prime hq]
  have hBsum : sumOfDivisors (2 ^ (k + 2) * r) = sumOfDivisors (2 ^ (k + 2)) * (r + 1) := by
    rw [sumOfDivisors_mul_of_coprime h2r, sumOfDivisors_prime hr]
  have hA : sumOfDivisors (2 ^ (k + 2)) + 1 = 2 ^ (k + 3) := sumOfDivisors_two_pow (k + 2)
  obtain ⟨g1, g2⟩ := thabit_identity k (sumOfDivisors (2 ^ (k + 2)) : ℕ) p q r
    (by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hA)
    (by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hpv)
    (by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hqv)
    (by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hrv)
  refine ⟨?_, ?_, ?_⟩
  · have hlt : p * q < r := by
      have hY : (1 : ℤ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      have hP : (p : ℤ) + 1 = 3 * 2 ^ (k + 1) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hpv
      have hQ : (q : ℤ) + 1 = 3 * 2 ^ (k + 2) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hqv
      have hR : (r : ℤ) + 1 = 9 * 2 ^ (2 * k + 3) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hrv
      have e1 : (2 : ℤ) ^ (k + 1) = 2 ^ k * 2 := by ring
      have e2 : (2 : ℤ) ^ (k + 2) = 2 ^ k * 4 := by ring
      have e4 : (2 : ℤ) ^ (2 * k + 3) = (2 ^ k) ^ 2 * 8 := by rw [two_mul, pow_add, pow_add]; ring
      rw [e1] at hP
      rw [e2] at hQ
      rw [e4] at hR
      have : (p : ℤ) * q < r := by nlinarith
      exact_mod_cast this
    have hpos : 0 < (2 : ℕ) ^ (k + 2) := Nat.two_pow_pos _
    have : 2 ^ (k + 2) * p * q < 2 ^ (k + 2) * r := by
      rw [mul_assoc]; exact mul_lt_mul_of_pos_left hlt hpos
    omega
  · rw [hAsum]; exact_mod_cast g1
  · rw [hBsum]; exact_mod_cast g2

/-- `k` is a *Thâbit index*: all three numbers appearing in Thâbit ibn Qurra's rule are
prime.  (For example `k = 0`, `k = 2` and `k = 4` are Thâbit indices, giving the amicable
pairs `(220, 284)`, `(17296, 18416)` and `(9363584, 9437056)`.) -/
