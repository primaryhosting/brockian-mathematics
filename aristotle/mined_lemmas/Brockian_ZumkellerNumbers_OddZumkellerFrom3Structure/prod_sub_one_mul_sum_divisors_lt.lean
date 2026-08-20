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
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Brockian.ZumkellerNumbers

/-- A natural number `n` is *Zumkeller* if it is positive and its set of divisors can be
split into two parts with equal sums. -/

theorem prod_sub_one_mul_sum_divisors_lt {n : ℕ} (hn : n ≠ 0) (hne : n.primeFactors.Nonempty) :
    (∏ p ∈ n.primeFactors, (p - 1)) * (∑ d ∈ n.divisors, d)
      < (∏ p ∈ n.primeFactors, p) * n := by
  have hdiv : ∑ d ∈ n.divisors, d
      = ∏ p ∈ n.primeFactors, ∑ k ∈ Finset.range (n.factorization p + 1), p ^ k :=
    Nat.sum_divisors hn
  have hnprod : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n :=
    Nat.factorization_prod_pow_eq_self hn
  have key : ∀ p ∈ n.primeFactors,
      (p - 1) * (∑ k ∈ Finset.range (n.factorization p + 1), p ^ k)
        < p * p ^ n.factorization p := by
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have hgeom : ∀ m : ℕ, (p - 1) * (∑ k ∈ Finset.range (m + 1), p ^ k) = p ^ (m + 1) - 1 := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
          rw [Finset.sum_range_succ, Nat.mul_add, ih]
          have hpm : 1 ≤ p ^ (m + 1) := Nat.one_le_pow _ _ (by omega)
          have hmul : (p - 1) * p ^ (m + 1) = p ^ (m + 1 + 1) - p ^ (m + 1) := by
            rw [Nat.sub_mul, one_mul, ← pow_succ']
          have hmono : p ^ (m + 1) ≤ p ^ (m + 1 + 1) :=
            Nat.pow_le_pow_right (by omega) (by omega)
          rw [hmul]
          omega
    rw [hgeom, ← pow_succ']
    have : 1 ≤ p ^ (n.factorization p + 1) := Nat.one_le_pow _ _ (by omega)
    omega
  calc (∏ p ∈ n.primeFactors, (p - 1)) * (∑ d ∈ n.divisors, d)
      = ∏ p ∈ n.primeFactors,
          ((p - 1) * ∑ k ∈ Finset.range (n.factorization p + 1), p ^ k) := by
        rw [hdiv, ← Finset.prod_mul_distrib]
    _ < ∏ p ∈ n.primeFactors, (p * p ^ n.factorization p) :=
        Finset.prod_lt_prod_of_nonempty
          (fun p hp => by
            have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
            have hs : 0 < ∑ k ∈ Finset.range (n.factorization p + 1), p ^ k := by
              refine Finset.sum_pos (fun k _ => pow_pos (show 0 < p by omega) k) ⟨0, ?_⟩
              exact Finset.mem_range.mpr (by omega)
            have : 0 < p - 1 := by omega
            positivity)
          key hne
    _ = (∏ p ∈ n.primeFactors, p) * n := by
        rw [Finset.prod_mul_distrib, hnprod]

/-- For odd `n` with at most two prime factors, `∏ p ≤ 2 * ∏ (p - 1)`. -/
