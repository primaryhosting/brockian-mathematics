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
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
The infinitude of amicable numbers is a well-known open problem.  What is proved here is a
*conditional reduction*: if Thabit ibn Qurra's rule produces amicable pairs for arbitrarily
large parameters (i.e. there are arbitrarily large `m` for which the three Thabit numbers
`3·2^m - 1`, `3·2^(m+1) - 1`, `9·2^(2m+1) - 1` are all prime), then there are infinitely many
amicable numbers.  The Thabit construction itself is proved unconditionally
(`Brockian.AmicableNumbers.isAmicablePair_thabit`), as is the classical example `(220, 284)`.
-/

namespace Brockian.AmicableNumbers

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- `a` and `b` form an amicable pair: they are distinct and each one's proper divisors sum to
the other, equivalently `σ a = σ b = a + b`. -/

private lemma coprime_two_pow_of_odd_prime {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Nat.Coprime (2 ^ n) p :=
  Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))

/-- Thabit ibn Qurra's rule, in the normalized parametrization `2 ^ m = B + 1`. -/
