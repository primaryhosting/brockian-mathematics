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
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- `sigmaOne n` is the sum of all divisors of `n`, usually written `σ₁ (n)`. -/

lemma isHyperperfect_one_of_mersenne {k q : ℕ} (hk : 1 ≤ k) (hq : q.Prime)
    (hqe : q + 1 = 2 ^ (k + 1)) : IsHyperperfect 1 (2 ^ k * q) := by
  have hq2 : 2 ≤ q := hq.two_le
  have hqodd : q ≠ 2 := by
    intro h
    rw [h] at hqe
    have : 2 ^ (1 + 1) ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hcop : Nat.Coprime (2 ^ k) q :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hq).2 (fun h => hqodd h.symm))
  have hsig : sigmaOne (2 ^ k * q) = q * (q + 1) := by
    unfold sigmaOne
    rw [Nat.Coprime.sum_divisors_mul hcop, hq.sum_divisors]
    have h1 := sigmaOne_two_pow k
    unfold sigmaOne at h1
    have h2 : (∑ d ∈ (2 ^ k).divisors, d) = q := by omega
    rw [h2]
  have h2k : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  refine ⟨by norm_num, ?_, ?_⟩
  · have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    calc 1 < 2 * 2 := by norm_num
      _ ≤ 2 ^ k * q := Nat.mul_le_mul (by omega) hq2
  · have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    have key : q * (q + 1) = 2 * (2 ^ k * q) := by rw [hqe, hpow]; ring
    rw [hsig, key]
    ring

/-- **Conditional infinitude of hyperperfect numbers, via Mersenne primes.**  If there are
infinitely many Mersenne primes, then there are infinitely many hyperperfect numbers (indeed
infinitely many `1`-hyperperfect, i.e. perfect, numbers). -/
