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
# Even Perfect Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.EvenPerfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib
import Archive.Wiedijk100Theorems.PerfectNumbers

/-!
# Even Perfect Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.EvenPerfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace MersennePerfect

/-- The set of even perfect natural numbers. -/

lemma mem_evenPerfects_of_mem_mersenneExponents {p : ℕ} (hp : p ∈ mersenneExponents) :
    2 ^ (p - 1) * mersenne p ∈ evenPerfects := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := by
    cases p with
    | zero => simp [mersenneExponents, mersenne, Nat.not_prime_zero] at hp
    | succ k => exact ⟨k, rfl⟩
  simpa using
    ⟨Theorems100.Nat.even_two_pow_mul_mersenne_of_prime k hp,
      Theorems100.Nat.perfect_two_pow_mul_mersenne_of_prime k hp⟩

/-- **Even Perfect Infinitude**: there are infinitely many even perfect numbers if and only if
there are infinitely many Mersenne primes.  (Both sides are open problems; this is the
Euclid–Euler reduction of one to the other.) -/
