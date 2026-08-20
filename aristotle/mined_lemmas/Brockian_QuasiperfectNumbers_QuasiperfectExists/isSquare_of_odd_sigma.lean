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
A natural number `n` is *quasiperfect* if `σ n = 2 * n + 1`, i.e. the sum of the proper
divisors of `n` (including `1`) equals `n + 1`.  No quasiperfect number is known, and their
existence is an open problem.

This file proves the classical structural constraints (Cattaneo, 1951): a quasiperfect number
must be an odd perfect square, and it cannot be a prime power.  The main theorem
`QuasiperfectExists` is the resulting *reduction*: a quasiperfect number exists if and only if
there is an odd `k > 1`, not a prime power, whose square is quasiperfect.
-/

namespace Brockian.QuasiperfectNumbers

open Finset

/-- A natural number `n` is *quasiperfect* if it is positive and the sum of all of its
divisors equals `2 * n + 1`. -/

theorem isSquare_of_odd_sigma {n : ℕ} (hn : n ≠ 0) (hodd : Odd n)
    (h : Odd (∑ d ∈ n.divisors, d)) : IsSquare n := by
  have hcard : (∑ d ∈ n.divisors, d) % 2 = n.divisors.card % 2 := by
    rw [Finset.sum_nat_mod]
    have hd1 : ∀ d ∈ n.divisors, d % 2 = 1 := fun d hd =>
      Nat.odd_iff.mp (hodd.of_dvd_nat (Nat.dvd_of_mem_divisors hd))
    rw [Finset.sum_congr rfl hd1]
    simp
  have h2 : Odd n.divisors.card := by rw [Nat.odd_iff] at *; omega
  rw [Nat.card_divisors hn] at h2
  have hall : ∀ p ∈ n.primeFactors, Even (n.factorization p) := by
    intro p hp
    have hnd : ¬ (2 ∣ ∏ x ∈ n.primeFactors, (n.factorization x + 1)) := by
      rw [Nat.odd_iff] at h2; omega
    have h3 := (Nat.prime_two.prime.dvd_finset_prod_iff _).not.mp hnd
    push_neg at h3
    have h4 := h3 p hp
    rcases Nat.even_or_odd (n.factorization p) with he | ho
    · exact he
    · exact absurd (by rw [Nat.odd_iff] at ho; omega) h4
  refine ⟨∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2), ?_⟩
  rw [← Finset.prod_mul_distrib]
  conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
  rw [Nat.prod_factorization_eq_prod_primeFactors]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [← pow_add]
  congr 1
  obtain ⟨k, hk⟩ := hall p hp
  omega

/-- The key quadratic-residue obstruction: a number `N ≡ 3 [MOD 4]` cannot divide `m + 1`
for a perfect square `m`, since otherwise `-1` would be a square modulo `N`. -/
