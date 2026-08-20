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
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Zumkeller From 3 Structure

A *Zumkeller number* is a positive integer whose divisors can be split into two sets with
equal sums.  Here we prove that an odd Zumkeller number must have at least three distinct
prime factors.

The argument: a Zumkeller number is perfect or abundant (`σ(n) ≥ 2n`), while an odd number
with at most two distinct prime factors `p < q` satisfies
`σ(n)/n < p/(p-1) · q/(q-1) ≤ (3/2)(5/4) < 2`, hence is deficient.
-/

open scoped BigOperators

set_option maxRecDepth 40000

namespace Brockian.ZumkellerNumbers

/-- `n` is a *Zumkeller number* if it is positive and its set of divisors can be split into
two parts having the same sum. -/

theorem prod_pred_mul_sigma_le : ∀ n : ℕ, 0 < n →
    (∏ p ∈ n.primeFactors, (p - 1)) * (∑ d ∈ n.divisors, d)
      ≤ (∏ p ∈ n.primeFactors, p) * n := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
      intro _
      have hpf : (p ^ k).primeFactors = {p} := Nat.primeFactors_prime_pow hk.ne' hp
      rw [hpf]
      simp only [Finset.prod_singleton]
      rw [Nat.sum_divisors_prime_pow hp (f := fun x => x)]
      obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
      simp only [Nat.add_sub_cancel]
      have hg := geom_sum_nat m (k + 1)
      calc m * (∑ i ∈ Finset.range (k + 1), (m + 1) ^ i) ≤ (m + 1) ^ (k + 1) := by omega
        _ = (m + 1) * (m + 1) ^ k := by ring
  | zero => omega
  | one => simp
  | coprime a b ha hb hab iha ihb =>
      intro _
      have ha0 : 0 < a := by omega
      have hb0 : 0 < b := by omega
      rw [hab.primeFactors_mul, Finset.prod_union hab.disjoint_primeFactors,
        Finset.prod_union hab.disjoint_primeFactors, hab.sum_divisors_mul]
      calc ((∏ p ∈ a.primeFactors, (p - 1)) * (∏ p ∈ b.primeFactors, (p - 1))) *
            ((∑ d ∈ a.divisors, d) * (∑ d ∈ b.divisors, d))
          = ((∏ p ∈ a.primeFactors, (p - 1)) * (∑ d ∈ a.divisors, d)) *
            ((∏ p ∈ b.primeFactors, (p - 1)) * (∑ d ∈ b.divisors, d)) := by ring
        _ ≤ ((∏ p ∈ a.primeFactors, p) * a) * ((∏ p ∈ b.primeFactors, p) * b) :=
            Nat.mul_le_mul (iha ha0) (ihb hb0)
        _ = ((∏ p ∈ a.primeFactors, p) * (∏ p ∈ b.primeFactors, p)) * (a * b) := by ring

/-- For an odd number with at most two distinct prime factors, `∏ p < 2 * ∏ (p - 1)`. -/
