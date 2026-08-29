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
-- (Lean requires `import` commands to precede any module doc comment `/-! ... -/`,
-- so the header is repeated verbatim as a module docstring just below the import.)

import Mathlib

/-!
# Mersenne Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.MersennePrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The infinitude of Mersenne primes is a famous open problem, so we do not prove it
outright.  Instead we give a Lean-checked *equivalent reformulation*: the set of
exponents `p` for which `2 ^ p - 1` is prime is infinite **if and only if** the set of
even perfect numbers is infinite.  The equivalence comes from the Euclid–Euler
theorem, which is reproved here (following the Mathlib archive development of the
Euclid–Euler theorem) so that the file depends only on `Mathlib` itself.

We also record the contrapositive form: there are only finitely many Mersenne primes
iff there are only finitely many even perfect numbers.
-/

namespace Brockian

namespace MersennePerfect

open ArithmeticFunction Finset

open scoped sigma

/-! ### The Euclid–Euler theorem -/


theorem image_euclidEuler : euclidEuler '' MersenneExponents = EvenPerfects := by
  ext n
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 :=
      ⟨p - 1, by have := pos_of_mem_mersenneExponents hp; omega⟩
    have hpr : Nat.Prime (mersenne (k + 1)) := hp
    refine even_and_perfect_iff.mpr ⟨k, hpr, ?_⟩
    simp [euclidEuler]
  · rintro ⟨hev, hperf⟩
    obtain ⟨k, hpr, rfl⟩ := even_and_perfect_iff.mp ⟨hev, hperf⟩
    exact ⟨k + 1, hpr, by simp [euclidEuler]⟩

/-! ### Main result -/

/-- **Reformulation of the Mersenne prime infinitude conjecture.**

There are infinitely many Mersenne primes (i.e. infinitely many exponents `p` with
`2 ^ p - 1` prime) if and only if there are infinitely many even perfect numbers.

The infinitude itself is an open problem; this is a Lean-checked equivalent
reformulation, obtained from the Euclid–Euler theorem. -/
