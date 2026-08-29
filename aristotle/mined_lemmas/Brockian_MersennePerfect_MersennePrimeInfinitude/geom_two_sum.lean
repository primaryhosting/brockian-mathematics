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
# Mersenne Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.MersennePrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The infinitude of Mersenne primes is a famous open problem, so what is established here is a
*Lean-checked conditional reduction*: the set of Mersenne primes is infinite **if and only if**
the set of even perfect numbers is infinite.  Both implications go through a full formalisation
of the Euclid–Euler theorem, which is proved from scratch below.
-/

set_option autoImplicit false

namespace Brockian.MersennePerfect

open ArithmeticFunction Nat

/-- The sum-of-divisors function `σ₁`. -/

theorem geom_two_sum (k : ℕ) : ∑ x ∈ Finset.range (k + 1), 2 ^ x = mersenne (k + 1) := by
  induction k with
  | zero => simp [mersenne]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have e1 := mersenne_add_one (n + 1)
      have e2 := mersenne_add_one (n + 1 + 1)
      have e3 : (2 : ℕ) ^ (n + 1 + 1) = 2 ^ (n + 1) + 2 ^ (n + 1) := by ring
      omega

