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
## Overview

Whether there are infinitely many even perfect numbers is a well-known open problem: by the
Euclid–Euler theorem it is *equivalent* to the existence of infinitely many Mersenne primes,
which is itself open.  Accordingly, what is proved here is the (unconditional, Lean-checked)
reduction:

* `Brockian.MersennePerfect.EvenPerfectInfinitude` :
  if there are infinitely many exponents `p` with `mersenne p = 2 ^ p - 1` prime, then the set
  of even perfect numbers is infinite.

The file is self-contained over Mathlib: Euclid's direction of the Euclid–Euler theorem
(a Mersenne prime yields an even perfect number) is proved here from scratch.
-/

namespace Brockian.MersennePerfect

open ArithmeticFunction Finset

-- access notation `σ`
open scoped sigma

/-- The set of exponents `p` for which the Mersenne number `2 ^ p - 1` is prime. -/

theorem even_two_pow_mul_mersenne {k : ℕ} (pr : (mersenne (k + 1)).Prime) :
    Even (2 ^ k * mersenne (k + 1)) := by
  simp [exponent_ne_zero pr, parity_simps]

/-- Euclid's construction lands in the set of even perfect numbers. -/
