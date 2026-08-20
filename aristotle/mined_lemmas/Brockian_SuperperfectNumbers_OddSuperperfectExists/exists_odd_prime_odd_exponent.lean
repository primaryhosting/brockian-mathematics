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

lemma exists_odd_prime_odd_exponent {n : ℕ} (hn : Odd n) (h : Superperfect n) :
    ∃ p, p.Prime ∧ p ≠ 2 ∧ Odd ((σ 1 n).factorization p) := by
  by_contra hcon
  push_neg at hcon
  have hn0 : n ≠ 0 := hn.pos.ne'
  have hM0 : σ 1 n ≠ 0 := fun hz => hn0 (sigma_eq_zero.mp hz)
  have hodd : Odd (σ 1 (σ 1 n)) := by
    refine odd_sigma_of_even_factorization hM0 ?_
    intro p hp hne
    exact Nat.not_odd_iff_even.1 (hcon p (Nat.prime_of_mem_primeFactors hp) hne)
  rw [h] at hodd
  exact (Nat.not_odd_iff_even.2 (even_two_mul n)) hodd

set_option maxRecDepth 8000000 in
