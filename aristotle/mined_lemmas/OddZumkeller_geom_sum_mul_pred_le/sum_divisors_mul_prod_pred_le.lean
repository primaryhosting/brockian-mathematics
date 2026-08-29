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

namespace OddZumkeller

/-- A positive natural number `n` is a *Zumkeller number* if its set of divisors can be split
into two parts having the same sum. -/

lemma sum_divisors_mul_prod_pred_le (n : ℕ) :
    (∑ d ∈ n.divisors, d) * ∏ p ∈ n.primeFactors, (p - 1)
      ≤ n * ∏ p ∈ n.primeFactors, p := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
      have hpf : (p ^ k).primeFactors = {p} := by
        rw [Nat.primeFactors_pow _ hk.ne', hp.primeFactors]
      rw [hpf, Nat.sum_divisors_prime_pow hp]
      simp only [Finset.prod_singleton]
      calc (∑ i ∈ Finset.range (k + 1), p ^ i) * (p - 1)
          ≤ p ^ (k + 1) := geom_sum_mul_pred_le p k hp.one_lt.le
        _ = p ^ k * p := pow_succ p k
  | zero => simp
  | one => simp
  | coprime a b ha hb hab iha ihb =>
      have ha0 : a ≠ 0 := by omega
      have hb0 : b ≠ 0 := by omega
      have hdisj : Disjoint a.primeFactors b.primeFactors := Nat.Coprime.disjoint_primeFactors hab
      rw [hab.sum_divisors_mul, Nat.primeFactors_mul ha0 hb0, Finset.prod_union hdisj,
        Finset.prod_union hdisj]
      calc ((∑ d ∈ a.divisors, d) * ∑ d ∈ b.divisors, d) *
            ((∏ p ∈ a.primeFactors, (p - 1)) * ∏ p ∈ b.primeFactors, (p - 1))
          = ((∑ d ∈ a.divisors, d) * ∏ p ∈ a.primeFactors, (p - 1)) *
            ((∑ d ∈ b.divisors, d) * ∏ p ∈ b.primeFactors, (p - 1)) := by ring
        _ ≤ (a * ∏ p ∈ a.primeFactors, p) * (b * ∏ p ∈ b.primeFactors, p) :=
            Nat.mul_le_mul iha ihb
        _ = a * b * ((∏ p ∈ a.primeFactors, p) * ∏ p ∈ b.primeFactors, p) := by ring

/-- A Zumkeller number is perfect or abundant: `2 * n ≤ σ n`. -/
