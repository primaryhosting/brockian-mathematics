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


open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace Brockian.HyperperfectNumbers

/-- `n` is `k`-hyperperfect if `n = 1 + k * (σ n - n - 1)`, i.e. `n` is one plus `k` times the
sum of its proper divisors other than `1`.  The definition is stated in the subtraction-free
form `k * σ n + 1 = (k + 1) * n + k`. -/

theorem isKHyperperfect_minoli {q p t : ℕ} (hq : q.Prime) (hp : p.Prime) (ht : 2 ≤ t)
    (hpq : q ^ t + 1 = p + q) :
    IsKHyperperfect (q - 1) (q ^ (t - 1) * p) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by have := hq.two_le; omega⟩
  set q := r + 1 with hqdef
  have hr : 1 ≤ r := by have := hq.two_le; omega
  -- `p > q`
  have hq2 : q * q ≤ q ^ t := by
    calc q * q = q ^ 2 := by ring
    _ ≤ q ^ t := Nat.pow_le_pow_right (by omega) ht
  have hpgt : q < p := by nlinarith [hq.two_le]
  have hne : q ≠ p := by omega
  -- factorisation of σ
  have hcop : Nat.Coprime (q ^ (t - 1)) p :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes hq hp).mpr hne)
  have hsig : σ 1 (q ^ (t - 1) * p) = (∑ k ∈ range t, q ^ k) * (p + 1) := by
    rw [isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_one_apply_prime_pow hq,
      show p = p ^ 1 from (pow_one p).symm, sigma_one_apply_prime_pow hp]
    have h : t - 1 + 1 = t := by omega
    rw [h]
    simp [Finset.sum_range_succ, pow_one, add_comm]
  -- the arithmetic identity
  have hgeom := geom_aux r t
  have hpow : q ^ t = q * q ^ (t - 1) := by
    conv_lhs => rw [show t = (t - 1) + 1 by omega]
    ring
  refine ⟨by omega, ?_, ?_⟩
  · have h1 : 2 ≤ q ^ (t - 1) := by
      calc 2 ≤ q := hq.two_le
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ (t - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith [hp.two_le]
  · have hA : (q - 1) * σ 1 (q ^ (t - 1) * p) = (r * ∑ k ∈ range t, q ^ k) * (p + 1) := by
      rw [hsig]; simp [hqdef, mul_assoc]
    rw [hA]
    set A := r * ∑ k ∈ range t, q ^ k with hAdef
    have h1 : A + 1 = q ^ t := hgeom
    have h2 : p + r = A + 1 := by omega
    have h3 : (q - 1 + 1) * (q ^ (t - 1) * p) = (A + 1) * p := by
      rw [show q - 1 + 1 = q by omega, ← mul_assoc, ← hpow, h1]
    rw [h3, show q - 1 = r by omega]
    nlinarith

/-- The Euclid–Mersenne special case: if `2 ^ t - 1` is prime (`t ≥ 2`), then
`2 ^ (t - 1) * (2 ^ t - 1)` is `1`-hyperperfect, i.e. perfect. -/
