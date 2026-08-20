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

import Mathlib

/-!
# Mersenne Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.MersennePrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The infinitude of Mersenne primes is a famous open problem, so what is established here is a
*Lean-checked conditional reduction*: the set of Mersenne prime exponents is infinite **iff**
the set of even perfect numbers is infinite.  This is obtained from an explicit, unconditional
bijection (Euclid–Euler): the strictly monotone map `k ↦ 2 ^ (k - 1) * (2 ^ k - 1)` carries the
set of exponents `k` with `2 ^ k - 1` prime *onto* the set of even perfect numbers.

The proof of the Euclid–Euler theorem itself is reproduced here (it lives in the `Archive`
component of Mathlib, which is not importable from this project); the argument follows
`Archive/Wiedijk100Theorems/PerfectNumbers.lean` by Aaron Anderson.
-/

namespace Brockian.MersennePerfect

open ArithmeticFunction Finset
open scoped sigma

/-! ## Euclid–Euler -/


def EvenPerfects : Set ℕ := {n : ℕ | Even n ∧ n.Perfect}

/-- The Euclid–Euler map `k ↦ 2 ^ (k - 1) * (2 ^ k - 1)`. -/
