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

open Finset

namespace Brockian.SuperperfectNumbers

/-- The sum-of-divisors function `σ(n) = ∑_{d ∣ n} d`. -/

lemma sigma1_factorization {m : ℕ} (hm : m ≠ 0) :
    sigma1 m = ∏ p ∈ m.primeFactors, sigma1 (p ^ m.factorization p) := by
  have h := (ArithmeticFunction.isMultiplicative_sigma (k := 1)).multiplicative_factorization _ hm
  simp only [sigma1, ← ArithmeticFunction.sigma_one_apply]
  rw [h, Finsupp.prod, Nat.support_factorization]

/-! ### The 2-adic behaviour of `σ` on prime powers -/

/-- `σ(2^e) = 2^{e+1} - 1` is odd. -/
