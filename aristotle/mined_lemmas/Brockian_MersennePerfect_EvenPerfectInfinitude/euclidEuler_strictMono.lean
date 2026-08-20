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

theorem euclidEuler_strictMono : StrictMono euclidEuler := by
  apply strictMono_nat_of_lt_succ
  intro k
  have h1 : (2 : ℕ) ^ k < 2 ^ (k + 1) :=
    Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self k)
  have h2 : mersenne (k + 1) < mersenne (k + 2) := by
    have h5 : (2 : ℕ) ^ (k + 1) < 2 ^ (k + 2) :=
      Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _)
    have h3 : 1 ≤ (2 : ℕ) ^ (k + 1) := Nat.one_le_two_pow
    simp only [mersenne]
    omega
  have h4 : 0 < mersenne (k + 1) := by
    have : 1 < (2 : ℕ) ^ (k + 1) := Nat.one_lt_two_pow (by omega)
    simp only [mersenne]; omega
  simpa [euclidEuler] using Nat.mul_lt_mul_of_lt_of_lt h1 h2

