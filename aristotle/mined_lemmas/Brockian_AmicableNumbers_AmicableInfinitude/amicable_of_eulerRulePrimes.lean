import Brockian.AmicableNumbers

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

open Finset

/-- `a` and `b` form an *amicable pair*: they are distinct and each is the sum of the
proper divisors of the other, equivalently `σ₁ a = σ₁ b = a + b`. -/

theorem amicable_of_eulerRulePrimes {m : ℕ} (h : EulerRulePrimes m) :
    Amicable (2 ^ (m + 2) * ((3 * 2 ^ (m + 1) - 1) * (3 * 2 ^ (m + 2) - 1)))
      (2 ^ (m + 2) * (9 * 2 ^ (2 * m + 3) - 1)) := by
  obtain ⟨hp, hq, hr⟩ := h
  -- write `2 ^ (m + 1) = Q + 2`
  have h2 : 2 ≤ 2 ^ (m + 1) := by
    calc (2:ℕ) = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨Q, hQ⟩ : ∃ Q, 2 ^ (m + 1) = Q + 2 := ⟨2 ^ (m + 1) - 2, by omega⟩
  have e2 : 2 ^ (m + 2) = 2 * (Q + 2) := by
    rw [show m + 2 = (m + 1) + 1 from rfl, pow_succ, hQ]; ring
  have e3 : 2 ^ (2 * m + 3) = 2 * ((Q + 2) * (Q + 2)) := by
    have : (2:ℕ) ^ (2 * m + 3) = 2 ^ (m + 1) * 2 ^ (m + 1) * 2 := by ring
    rw [this, hQ]; ring
  have hpv : 3 * 2 ^ (m + 1) - 1 = 3 * Q + 5 := by rw [hQ]; omega
  have hqv : 3 * 2 ^ (m + 2) - 1 = 6 * Q + 11 := by rw [e2]; omega
  have hrv : 9 * 2 ^ (2 * m + 3) - 1 = 18 * Q * Q + 72 * Q + 71 := by
    have h9 : 9 * (2 * ((Q + 2) * (Q + 2))) = 18 * Q * Q + 72 * Q + 72 := by ring
    rw [e3]; omega
  -- divisor sums
  have hs2 : (∑ d ∈ (2 ^ (m + 2)).divisors, d) = 4 * Q + 7 := by
    have := sum_divisors_two_pow (m + 2)
    have h4 : (2:ℕ) ^ (m + 2 + 1) = 4 * (Q + 2) := by
      rw [show m + 2 + 1 = (m + 1) + 2 from rfl, pow_succ, pow_succ, hQ]; ring
    omega
  -- coprimality facts
  have hodd : ∀ {x : ℕ}, x.Prime → x % 2 = 1 → Nat.Coprime (2 ^ (m + 2)) x := by
    intro x hx hx2
    refine Nat.Coprime.pow_left _ ?_
    rw [Nat.coprime_comm]
    exact (Nat.coprime_primes hx Nat.prime_two).mpr (by omega)
  have hcp : Nat.Coprime (2 ^ (m + 2)) (3 * 2 ^ (m + 1) - 1) := by
    refine hodd hp ?_
    rw [hpv]; omega
  have hcq : Nat.Coprime (2 ^ (m + 2)) (3 * 2 ^ (m + 2) - 1) := by
    refine hodd hq ?_
    rw [hqv]; omega
  have hcr : Nat.Coprime (2 ^ (m + 2)) (9 * 2 ^ (2 * m + 3) - 1) := by
    refine hodd hr ?_
    rw [hrv]; omega
  have hpq : Nat.Coprime (3 * 2 ^ (m + 1) - 1) (3 * 2 ^ (m + 2) - 1) := by
    refine (Nat.coprime_primes hp hq).mpr ?_
    rw [hpv, hqv]; omega
  -- the two divisor sums
  have hsa : (∑ d ∈ (2 ^ (m + 2) * ((3 * 2 ^ (m + 1) - 1) * (3 * 2 ^ (m + 2) - 1))).divisors, d)
      = (4 * Q + 7) * ((3 * Q + 6) * (6 * Q + 12)) := by
    rw [Nat.Coprime.sum_divisors_mul (hcp.mul_right hcq),
      Nat.Coprime.sum_divisors_mul hpq, hs2, sum_divisors_prime hp, sum_divisors_prime hq,
      hpv, hqv]
  have hsb : (∑ d ∈ (2 ^ (m + 2) * (9 * 2 ^ (2 * m + 3) - 1)).divisors, d)
      = (4 * Q + 7) * (18 * Q * Q + 72 * Q + 72) := by
    rw [Nat.Coprime.sum_divisors_mul hcr, hs2, sum_divisors_prime hr, hrv]
  refine ⟨?_, ?_, ?_⟩
  · rw [hpv, hqv, hrv, e2]
    have hlt : (3 * Q + 5) * (6 * Q + 11) < 18 * Q * Q + 72 * Q + 71 := by nlinarith
    exact Nat.ne_of_lt (mul_lt_mul_of_pos_left hlt (show 0 < 2 * (Q + 2) by omega))
  · rw [hsa, hpv, hqv, hrv, e2]; ring
  · rw [hsb, hpv, hqv, hrv, e2]; ring

/-! ### Sanity checks: the classical amicable pairs produced by Euler's rule -/

