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
# Quasiperfect Exists
Category: Brockian Conjecture
Target: Brockian.QuasiperfectNumbers.QuasiperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.QuasiperfectNumbers

open Finset

/-- A natural number `n` is *quasiperfect* if the sum of its divisors equals `2 * n + 1`,
i.e. the sum of its proper divisors is `n + 1`. -/

lemma isSquare_of_odd_card_divisors {n : ℕ} (hn : n ≠ 0) (h : Odd n.divisors.card) :
    IsSquare n := by
  rw [Nat.card_divisors hn] at h
  have heven : ∀ p ∈ n.primeFactors, Even (n.factorization p) := by
    intro p hp
    have hdvd : (n.factorization p + 1) ∣ ∏ x ∈ n.primeFactors, (n.factorization x + 1) :=
      Finset.dvd_prod_of_mem _ hp
    rcases Nat.even_or_odd (n.factorization p) with he | ho
    · exact he
    · exfalso
      rw [Nat.odd_iff] at h ho
      have h2 : 2 ∣ ∏ x ∈ n.primeFactors, (n.factorization x + 1) :=
        dvd_trans (by omega) hdvd
      omega
  have key : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
    conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hn]
    rw [Finsupp.prod, Nat.support_factorization]
  refine ⟨∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2), ?_⟩
  rw [← Finset.prod_mul_distrib]
  have hcongr : ∀ p ∈ n.primeFactors, p ^ (n.factorization p / 2) * p ^ (n.factorization p / 2)
      = p ^ (n.factorization p) := by
    intro p hp
    rw [← pow_add]
    congr 1
    obtain ⟨k, hk⟩ := heven p hp
    omega
  rw [Finset.prod_congr rfl hcongr, key]

/-- For odd `n`, the sum of divisors has the same parity as the number of divisors. -/
