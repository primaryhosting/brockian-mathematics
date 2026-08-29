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
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.HyperperfectNumbers

open Finset

/-- `sigma n` is the sum of all divisors of `n`. -/

lemma isHyperperfect_one_two_pow_mul_mersenne {k q : ℕ} (hq : q.Prime) (hqk : q + 1 = 2 ^ (k + 1))
    (hk : 1 ≤ k) : IsHyperperfect 1 (2 ^ k * q) := by
  have hcop : Nat.Coprime (2 ^ k) q := by
    have hq2 : q ≠ 2 := by
      rintro rfl
      have : (2 : ℕ) ^ (k + 1) = 3 := by omega
      have h4 : (4 : ℕ) ≤ 2 ^ (k + 1) := by
        calc (4 : ℕ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hq).2 (Ne.symm hq2))
  have hs : sigma (2 ^ k * q) = (2 ^ (k + 1) - 1) * (q + 1) := by
    have h2 : sigma (2 ^ k) = 2 ^ (k + 1) - 1 := by have := sigma_two_pow k; omega
    rw [sigma_mul_of_coprime hcop, sigma_prime hq, h2]
  have hq3 : 3 ≤ q := by
    have h4 : (4 : ℕ) ≤ 2 ^ (k + 1) := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h2k : 2 ≤ 2 ^ k := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hqq : (2 : ℕ) ^ (k + 1) - 1 = q := by omega
  rw [hqq] at hs
  refine ⟨one_pos, ?_, ?_⟩
  · nlinarith
  · rw [hs]
    have : 2 ^ k * 2 = 2 ^ (k + 1) := by rw [pow_succ]
    nlinarith [hqk]

/-- **Hyperperfect Infinitude (conditional, Mersenne version).**
If there are infinitely many Mersenne primes, then there are infinitely many hyperperfect
numbers (indeed infinitely many `1`-hyperperfect, i.e. perfect, numbers). -/
