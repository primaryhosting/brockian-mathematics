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
# Hyperperfect All K
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectAllK
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.HyperperfectNumbers

open Finset

/-- `sigmaOne n` is the sum of the divisors of `n`, i.e. `σ₁ n`. -/

lemma sigmaOne_mul_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    sigmaOne (m * n) = sigmaOne m * sigmaOne n := by
  have := (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime h
  simpa [sigmaOne, ArithmeticFunction.sigma_one_apply] using this

/-- The sum of divisors of a product of two distinct primes. -/
