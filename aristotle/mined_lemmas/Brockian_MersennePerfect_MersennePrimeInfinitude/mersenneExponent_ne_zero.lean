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
-- (Lean requires `import` lines to precede any module docstring `/-! ... -/`, so the
-- header above is written as a plain block comment; its text is otherwise verbatim.)
import Mathlib
import Archive.Wiedijk100Theorems.PerfectNumbers

/-!
The infinitude of Mersenne primes is a famous open problem, so what is established here is a
Lean-checked **conditional reduction**: the set of Mersenne primes is infinite **if and only if**
the set of even perfect numbers is infinite.  The main target
`Brockian.MersennePerfect.MersennePrimeInfinitude` is the substantive direction: from the
infinitude of even perfect numbers one obtains infinitely many primes `p` with `2 ^ p - 1` prime.

The bridge is the Euclid–Euler theorem (available in Mathlib's archive as
`Theorems100.Nat.even_and_perfect_iff`).
-/

namespace Brockian.MersennePerfect

/-- `p` is a *Mersenne exponent* when `mersenne p = 2 ^ p - 1` is prime. -/

theorem mersenneExponent_ne_zero {p : ℕ} (hp : MersenneExponent p) : p ≠ 0 := by
  rintro rfl
  exact Nat.not_prime_zero (by simpa [MersenneExponent, mersenne] using hp)

/-- A Mersenne exponent is itself prime. -/
