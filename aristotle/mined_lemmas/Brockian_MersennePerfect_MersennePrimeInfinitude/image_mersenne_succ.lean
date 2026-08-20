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

import Archive.Wiedijk100Theorems.PerfectNumbers

/-!
Whether there are infinitely many Mersenne primes is a famous open problem, so we prove a
Lean-checked *conditional reduction*: the set of Mersenne primes is infinite **if and only if**
the set of even perfect numbers is infinite.

The mathematical input is the Euclid–Euler theorem, available in Mathlib's archive as
`Theorems100.Nat.even_and_perfect_iff`.
-/

namespace Brockian
namespace MersennePerfect

open Nat

/-- The set of Mersenne primes: primes of the form `2 ^ k - 1`. -/

lemma image_mersenne_succ :
    (fun k : ℕ => mersenne (k + 1)) '' mersenneExponents = mersennePrimes := by
  ext p
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨hk, ⟨k + 1, rfl⟩⟩
  · rintro ⟨hp, j, rfl⟩
    match j with
    | 0 => simp [mersenne, Nat.not_prime_zero] at hp
    | (k + 1) => exact ⟨k, hp, rfl⟩

/-- Euclid–Euler: the even perfect numbers are exactly the numbers `2 ^ k * (2 ^ (k + 1) - 1)`
for `k` a Mersenne exponent. -/
