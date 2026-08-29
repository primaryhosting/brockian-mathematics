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

/-- `IsKHyperperfect k n` states that `n` is a `k`-hyperperfect number, i.e. `k > 0`, `n > 1` and
`n = 1 + k * (σ n - n - 1)`, written here in the subtraction-free form
`k * σ n + 1 = (k + 1) * n + k`. -/

theorem isKHyperperfect_pow_mul_prime {k j p : ℕ} (hk : 0 < k) (hq : Nat.Prime (k + 1))
    (hj : 0 < j) (hp : p.Prime) (hpk : p + k = (k + 1) ^ (j + 1)) :
    IsKHyperperfect k ((k + 1) ^ j * p) := by
  -- `p` is strictly larger than `k + 1`
  have hlt : k + 1 < p := by
    have h2 : (k + 1) ^ 2 ≤ (k + 1) ^ (j + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hsq : (k + 1) ^ 2 = k * k + 2 * k + 1 := by ring
    nlinarith [hpk, h2]
  have hne : k + 1 ≠ p := by omega
  have hcop : Nat.Coprime ((k + 1) ^ j) p :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes hq hp).mpr hne)
  refine ⟨hk, ?_, ?_⟩
  · have h1 : 1 < p := hp.one_lt
    have hone : 1 ≤ (k + 1) ^ j := Nat.one_le_pow _ _ (by omega)
    calc 1 < p := h1
      _ = 1 * p := (one_mul p).symm
      _ ≤ (k + 1) ^ j * p := Nat.mul_le_mul_right _ hone
  · -- compute the divisor sum
    set S := ∑ i ∈ range (j + 1), (k + 1) ^ i with hS
    have hsig : ArithmeticFunction.sigma 1 ((k + 1) ^ j * p) = S * (p + 1) := by
      rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        sigma_one_prime_pow hq, sigma_one_prime hp, ← hS]
    have hA : k * S + 1 = p + k := by rw [hS, geom_sum_succ, ← hpk]
    have hpow : (k + 1) * ((k + 1) ^ j * p) = (p + k) * p := by
      rw [← Nat.mul_assoc, ← pow_succ' (k + 1) j, ← hpk]
    rw [hsig, hpow]
    calc k * (S * (p + 1)) + 1 = (k * S) * p + (k * S + 1) := by ring
      _ = (k * S) * p + (p + k) := by rw [hA]
      _ = (k * S + 1) * p + k := by ring
      _ = (p + k) * p + k := by rw [hA]

/-- Any `k`-hyperperfect number is hyperperfect. -/
