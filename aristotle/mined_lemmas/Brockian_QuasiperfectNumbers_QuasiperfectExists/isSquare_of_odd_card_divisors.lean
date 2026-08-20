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
# Quasiperfect Exists
Category: Brockian Conjecture
Target: Brockian.QuasiperfectNumbers.QuasiperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Quasiperfect numbers

A natural number `n` is *quasiperfect* if `σ(n) = 2n + 1`, i.e. the sum of its proper divisors
is `n + 1`. Whether a quasiperfect number exists is a well-known open problem; none is known.

This file records a **conditional reduction**: the existence of a quasiperfect number is
equivalent to the existence of one satisfying several necessary structural conditions
(`Brockian.QuasiperfectNumbers.QuasiperfectExists`). Along the way we prove, unconditionally:

* no prime power is quasiperfect (`not_quasiperfect_prime_pow`);
* every quasiperfect number is of the form `2 ^ a * m ^ 2` (`Quasiperfect.eq_two_pow_mul_sq`),
  since `σ(n) = 2n + 1` is odd;
* in particular an odd quasiperfect number is a perfect square (`Quasiperfect.isSquare_of_odd`);
* no quasiperfect number is squarefree (`Quasiperfect.not_squarefree`), and no quasiperfect
  number is perfect (`Quasiperfect.not_perfect`);
* there is no quasiperfect number below `101` (`not_quasiperfect_of_lt_101`).
-/

namespace Brockian.QuasiperfectNumbers

open Finset

/-- A natural number `n` is *quasiperfect* if it is positive and the sum of its divisors
equals `2 * n + 1` (equivalently, the sum of its proper divisors is `n + 1`).
No quasiperfect number is known; their existence is an open problem. -/

lemma isSquare_of_odd_card_divisors {n : ℕ} (hn : n ≠ 0) (h : Odd (#n.divisors)) :
    IsSquare n := by
  rw [Nat.card_divisors hn] at h
  have heven : ∀ p ∈ n.primeFactors, 2 ∣ n.factorization p := by
    intro p hp
    by_contra hodd
    have h2 : 2 ∣ (n.factorization p + 1) := by omega
    have : 2 ∣ ∏ x ∈ n.primeFactors, (n.factorization x + 1) :=
      h2.trans (Finset.dvd_prod_of_mem _ hp)
    rw [Nat.odd_iff] at h
    omega
  refine ⟨∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2), ?_⟩
  rw [← Finset.prod_mul_distrib]
  conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
  rw [Nat.prod_factorization_eq_prod_primeFactors]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [← pow_add]
  have := heven p hp
  congr 1
  omega

/-- An odd number with an odd sum of divisors is a perfect square. -/
