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
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

A natural number `n` is *superperfect* when `σ (σ n) = 2 n`.  Suryanarayana and Kanold
showed that the even superperfect numbers are exactly the powers `2 ^ k` with
`2 ^ (k + 1) - 1` prime; whether an *odd* superperfect number exists is an open problem.

This file contains a Lean-checked reduction of that open problem, together with the
(easy half of the) even classification and two unconditional constraints on a
hypothetical odd superperfect number.
-/

open scoped ArithmeticFunction.sigma

open ArithmeticFunction Finset

namespace Brockian.SuperperfectNumbers

/-- A natural number `n` is *superperfect* if `σ (σ n) = 2 * n`, where `σ` is the
sum-of-divisors function. -/

lemma odd_sigma_of_even_factorization {m : ℕ} (hm : m ≠ 0)
    (h : ∀ p ∈ m.primeFactors, p ≠ 2 → Even (m.factorization p)) : Odd (σ 1 m) := by
  rw [sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hm]
  apply Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one
  intro p hp
  simp only [mul_one]
  rcases eq_or_ne p 2 with rfl | hne
  · exact odd_geom_even (by decide) _
  · exact odd_geom_odd (Nat.Prime.odd_of_ne_two (Nat.prime_of_mem_primeFactors hp) hne)
      (h p hp hne)

/-! ### Constraints on a hypothetical odd superperfect number -/

/-- For an odd superperfect number `n`, some odd prime divides `σ n` to an odd power.
In particular `σ n` is neither a perfect square nor twice a perfect square. -/
