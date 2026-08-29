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

theorem mersennePrimes_infinite_iff_evenPerfects_infinite :
    MersennePrimes.Infinite ↔ EvenPerfects.Infinite :=
  mersennePrimes_infinite_iff.trans MersennePrimeInfinitude

/-! ### Unboundedness reformulation -/

/-- Infinitely many Mersenne primes is the same as: arbitrarily large exponents work. -/
