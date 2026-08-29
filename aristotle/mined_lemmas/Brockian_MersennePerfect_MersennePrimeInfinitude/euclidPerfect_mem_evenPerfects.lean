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
# Mersenne Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.MersennePrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment rather than a module docstring `/-!`,
-- because Lean 4 requires `import` commands to precede any module docstring.)

import Mathlib
import Archive.Wiedijk100Theorems.PerfectNumbers

/-!
The unconditional statement "there are infinitely many Mersenne primes" is a famous open
problem, so what is proved here is a Lean-checked *reduction*: the set of Mersenne prime
exponents is infinite **iff** the set of even perfect numbers is infinite.  The reduction
goes through the Euclid–Euler correspondence.
-/

namespace Brockian.MersennePerfect

/-- The set of exponents `p` for which `mersenne p = 2 ^ p - 1` is prime. -/

lemma euclidPerfect_mem_evenPerfects {p : ℕ} (hp : p ∈ MersenneExponents) :
    euclidPerfect p ∈ EvenPerfects := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 :=
    ⟨p - 1, by have := two_le_of_mem_mersenneExponents hp; omega⟩
  have hpr : (mersenne (k + 1)).Prime := hp
  refine ⟨?_, ?_⟩
  · simpa [euclidPerfect] using Theorems100.Nat.even_two_pow_mul_mersenne_of_prime k hpr
  · simpa [euclidPerfect] using Theorems100.Nat.perfect_two_pow_mul_mersenne_of_prime k hpr

