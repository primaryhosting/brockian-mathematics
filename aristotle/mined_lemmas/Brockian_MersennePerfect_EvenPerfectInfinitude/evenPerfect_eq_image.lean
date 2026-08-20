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

theorem evenPerfect_eq_image :
    {n : ℕ | Even n ∧ Nat.Perfect n} = euclidEuler '' {k : ℕ | Nat.Prime (mersenne (k + 1))} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_image, euclidEuler]
  rw [even_and_perfect_iff]
  constructor
  · rintro ⟨k, pr, rfl⟩; exact ⟨k, pr, rfl⟩
  · rintro ⟨k, pr, rfl⟩; exact ⟨k, pr, rfl⟩

/-- **Even Perfect Infinitude (reduction).**  There are infinitely many even perfect numbers
if and only if there are infinitely many Mersenne primes, i.e. infinitely many exponents `k`
with `2 ^ (k+1) - 1` prime. -/
