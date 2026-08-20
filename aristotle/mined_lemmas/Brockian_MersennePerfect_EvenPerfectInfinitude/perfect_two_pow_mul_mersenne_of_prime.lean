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

/-!
# Even Perfect Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.EvenPerfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Whether there are infinitely many even perfect numbers is a famous open problem, equivalent
to the infinitude of Mersenne primes.  What is proved here is exactly that equivalence: the
set of even perfect numbers is infinite **iff** the set of Mersenne primes is infinite.

The mathematical input is the Euclid–Euler theorem.  Mathlib contains it in the
`Archive` (see `Archive/Wiedijk100Theorems/PerfectNumbers.lean`, Theorem 70 of the
100 Theorems list, by Aaron Anderson), but the `Archive` is not importable from a
downstream project, so the relevant statements are reproved here, following that file.
-/

namespace Brockian

namespace MersennePerfect

open ArithmeticFunction Finset

open scoped sigma

/-- `σ 1 (2 ^ k) = 2 ^ (k+1) - 1`. -/

theorem perfect_two_pow_mul_mersenne_of_prime (k : ℕ) (pr : (mersenne (k + 1)).Prime) :
    Nat.Perfect (2 ^ k * mersenne (k + 1)) := by
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul, ← mul_assoc, ← pow_succ', ← sigma_one_apply,
    mul_comm,
    isMultiplicative_sigma.map_mul_of_coprime ((Odd.coprime_two_right (by simp)).pow_right _),
    sigma_two_pow_eq_mersenne_succ]
  · simp [pr, sigma_one_apply]
  · positivity

