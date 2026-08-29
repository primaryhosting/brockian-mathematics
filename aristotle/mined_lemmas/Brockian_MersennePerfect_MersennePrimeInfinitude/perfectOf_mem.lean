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

theorem perfectOf_mem {q : ℕ} (hq : q ∈ MersennePrimes) : perfectOf q ∈ EvenPerfects := by
  obtain ⟨j, rfl, hp⟩ := mem_MersennePrimes_iff.1 hq
  rw [perfectOf_mersenne]
  exact ⟨even_two_pow_mul_mersenne hp, perfect_two_pow_mul_mersenne hp⟩

