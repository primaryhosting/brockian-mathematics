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

A natural number `n` is *quasiperfect* if `σ(n) = 2n + 1`, i.e. the sum of its proper
divisors is `n + 1`.  No quasiperfect number is known, and their existence is a
long-standing open problem.

This file proves Cattaneo's theorem — every quasiperfect number is an odd perfect
square — and deduces from it the conditional reduction
`Brockian.QuasiperfectNumbers.QuasiperfectExists`: a quasiperfect number exists if and
only if a quasiperfect number that is an odd perfect square exists.
-/

namespace Brockian.QuasiperfectNumbers

open Finset

/-- `sigmaSum n` is the sum of all positive divisors of `n`. -/

lemma factorization_even_of_card_divisors_odd {x : ℕ} (hx : x ≠ 0)
    (hcard : Odd x.divisors.card) (p : ℕ) : Even (x.factorization p) := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  have hp : p ∈ x.primeFactors := by
    by_contra hnp
    rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at hnp
    rw [hnp] at hodd
    simp at hodd
  have h2 : 2 ∣ (x.factorization p + 1) := by rcases hodd with ⟨k, hk⟩; omega
  have hdvd : 2 ∣ ∏ q ∈ x.primeFactors, (x.factorization q + 1) :=
    h2.trans (Finset.dvd_prod_of_mem _ hp)
  rw [← Nat.card_divisors hx, Nat.odd_iff] at *
  omega

/-- An odd number whose divisor sum is odd is a perfect square. -/
