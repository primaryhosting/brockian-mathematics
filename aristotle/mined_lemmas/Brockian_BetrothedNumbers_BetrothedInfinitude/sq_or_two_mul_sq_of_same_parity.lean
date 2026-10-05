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
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Betrothed (quasi-amicable) numbers

A pair `(m, n)` of distinct positive integers is *betrothed* (or *quasi-amicable*,
or a *reduced amicable pair*) when

  `σ m = σ n = m + n + 1`,

i.e. each of `m` and `n` is the sum of the *nontrivial* proper divisors of the other.
The smallest example is `(48, 75)`.

Whether there are infinitely many betrothed pairs is an open problem, so the target
theorem `BetrothedInfinitude` is stated here as a **Lean-checked conditional
reduction**: infinitude of betrothed pairs follows from a prime-pattern hypothesis
`PrimePatternUnbounded`, which asks for arbitrarily large solutions of a pair of
`σ`-equations in which the two "new" factors are primes.

The hypothesis is *not* vacuous: `isBetrothedPattern_16_25_3_3` exhibits the
solution `(a, b, p, q) = (16, 25, 3, 3)`, which produces the betrothed pair
`(48, 75)`.

Alongside the reduction, several unconditional facts are proved: the first three
betrothed pairs, that no member of a betrothed pair is prime, that both members are
at least `48`, that the set of betrothed pairs is infinite exactly when betrothed
numbers are unbounded, and a parity restriction (in a betrothed pair whose two members
have the same parity, each member is a square or twice a square).
-/

namespace Brockian
namespace BetrothedNumbers

open ArithmeticFunction

set_option maxRecDepth 100000

/-- `IsBetrothedPair m n` says that `m` and `n` are distinct positive integers with
`σ m = σ n = m + n + 1`; equivalently, each is the sum of the proper divisors of the
other, excluding `1`. -/

theorem sq_or_two_mul_sq_of_same_parity {m n : ℕ} (h : IsBetrothedPair m n)
    (hpar : m % 2 = n % 2) :
    (∃ k, m = k ^ 2 ∨ m = 2 * k ^ 2) ∧ (∃ k, n = k ^ 2 ∨ n = 2 * k ^ 2) := by
  obtain ⟨hm, hn, -, -, -⟩ := id h
  obtain ⟨hom, hon⟩ := odd_sigma_of_same_parity h hpar
  exact ⟨sq_or_two_mul_sq_of_odd_sigma m hm hom, sq_or_two_mul_sq_of_odd_sigma n hn hon⟩

/-- The partner of a betrothed number is unique: it is `σ m - m - 1`. -/
