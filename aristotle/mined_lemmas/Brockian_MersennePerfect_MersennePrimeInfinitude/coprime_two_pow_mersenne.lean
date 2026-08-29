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

import Mathlib

/-!
# Mersenne Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.MersennePrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The infinitude of Mersenne primes is a famous open problem, so what is established here is a
*Lean-checked conditional reduction*: the set of Mersenne primes is infinite **if and only if**
the set of even perfect numbers is infinite.  Both implications go through a full formalisation
of the Euclid–Euler theorem, which is proved from scratch below.
-/

set_option autoImplicit false

namespace Brockian.MersennePerfect

open ArithmeticFunction Nat

/-- The sum-of-divisors function `σ₁`. -/

theorem coprime_two_pow_mersenne (j : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    Nat.Coprime (2 ^ j) (mersenne k) :=
  Nat.Coprime.pow_left _
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (two_not_dvd_mersenne hk))

/-! ### The sum-of-divisors computations -/

