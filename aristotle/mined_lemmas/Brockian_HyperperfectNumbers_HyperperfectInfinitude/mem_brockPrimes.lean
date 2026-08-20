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
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.HyperperfectNumbers

open Finset

/-- `sigmaOne n` is the sum of all divisors of `n`, usually written `σ₁ (n)`. -/

lemma mem_brockPrimes : (3 : ℕ) ∈ BrockPrimes ∧ (7 : ℕ) ∈ BrockPrimes ∧ (13 : ℕ) ∈ BrockPrimes := by
  refine ⟨⟨by norm_num, ?_⟩, ⟨by norm_num, ?_⟩, ⟨by norm_num, ?_⟩⟩ <;> norm_num

/-! ### A second reduction: Mersenne primes

Every (even) perfect number is `1`-hyperperfect, so Euclid's construction gives a second
conditional route to infinitude. -/

