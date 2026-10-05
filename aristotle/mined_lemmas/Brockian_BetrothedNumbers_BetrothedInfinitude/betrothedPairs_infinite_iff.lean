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

theorem betrothedPairs_infinite_iff :
    BetrothedPairs.Infinite ↔ ∀ N : ℕ, ∃ m n : ℕ, N < m ∧ IsBetrothedPair m n := by
  constructor
  · intro hinf N
    by_contra hcon
    push_neg at hcon
    have hsub : Prod.fst '' BetrothedPairs ⊆ Set.Iic N := by
      rintro x ⟨⟨m, n⟩, hmem, rfl⟩
      exact Nat.not_lt.mp fun hlt => (hcon m n hlt) hmem
    have hinj : Set.InjOn Prod.fst BetrothedPairs := by
      rintro ⟨m, n⟩ hmn ⟨m', n'⟩ hmn' (heq : m = m')
      subst heq
      exact Prod.ext rfl (partner_unique hmn hmn')
    exact hinf (((Set.finite_Iic N).subset hsub).of_finite_image hinj)
  · intro H
    refine Set.Infinite.of_image Prod.fst (Set.infinite_of_not_bddAbove ?_)
    rintro ⟨B, hB⟩
    obtain ⟨m, n, hlt, hpair⟩ := H B
    exact absurd (hB ⟨(m, n), hpair, rfl⟩) (by omega)

/-! ### A prime-pattern reduction -/

/-- The prime pattern underlying the reduction: `a, b` are positive, `p, q` are primes
not dividing `a, b` respectively, and the two `σ`-equations defining a betrothed pair
hold for `m = a * p`, `n = b * q` after using multiplicativity of `σ`. -/
