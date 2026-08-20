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
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

namespace Brockian.ZumkellerNumbers

/-- A positive integer `n` is a *Zumkeller number* when its set of divisors can be split into
two parts with equal sums, i.e. there is `S ⊆ n.divisors` whose sum is half of `σ₁ n`. -/

theorem sigma_mul_prod_sub_one_le (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.divisors, d) * ∏ p ∈ n.primeFactors, (p - 1) ≤
      n * ∏ p ∈ n.primeFactors, p := by
  revert hn
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
      intro _
      rw [Nat.primeFactors_prime_pow hk.ne' hp, Finset.prod_singleton, Finset.prod_singleton]
      exact sigma_primePow_mul_sub_one_le hp k
  | zero => omega
  | one => simp
  | coprime a b ha hb hab iha ihb =>
      intro _
      have ha0 : 0 < a := by omega
      have hb0 : 0 < b := by omega
      have hdisj : Disjoint a.primeFactors b.primeFactors := Nat.Coprime.disjoint_primeFactors hab
      rw [hab.primeFactors_mul, Finset.prod_union hdisj, Finset.prod_union hdisj,
        hab.sum_divisors_mul]
      calc ((∑ d ∈ a.divisors, d) * ∑ d ∈ b.divisors, d) *
            ((∏ p ∈ a.primeFactors, (p - 1)) * ∏ p ∈ b.primeFactors, (p - 1))
          = ((∑ d ∈ a.divisors, d) * ∏ p ∈ a.primeFactors, (p - 1)) *
            ((∑ d ∈ b.divisors, d) * ∏ p ∈ b.primeFactors, (p - 1)) := by ring
        _ ≤ (a * ∏ p ∈ a.primeFactors, p) * (b * ∏ p ∈ b.primeFactors, p) :=
            Nat.mul_le_mul (iha ha0) (ihb hb0)
        _ = a * b * ((∏ p ∈ a.primeFactors, p) * ∏ p ∈ b.primeFactors, p) := by ring

/-- For a set of at most two odd primes, `∏ p < 2 * ∏ (p-1)`. -/
