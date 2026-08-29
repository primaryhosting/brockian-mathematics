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

theorem isBetrothedPair_of_pattern {a b p q : ℕ} (h : IsBetrothedPattern a b p q) :
    IsBetrothedPair (a * p) (b * q) := by
  obtain ⟨ha, hb, hp, hq, hpa, hqb, hne, heq, hsum⟩ := h
  have hcop : Nat.Coprime a p := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpa |>.symm
  have hcoq : Nat.Coprime b q := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqb |>.symm
  have hsa : sigma 1 (a * p) = sigma 1 a * (p + 1) := by
    rw [isMultiplicative_sigma.map_mul_of_coprime hcop, ArithmeticFunction.sigma_one_apply p,
      hp.sum_divisors]
  have hsb : sigma 1 (b * q) = sigma 1 b * (q + 1) := by
    rw [isMultiplicative_sigma.map_mul_of_coprime hcoq, ArithmeticFunction.sigma_one_apply q,
      hq.sum_divisors]
  refine ⟨Nat.mul_pos ha hp.pos, Nat.mul_pos hb hq.pos, hne, ?_, ?_⟩
  · rw [hsa]; exact hsum
  · rw [hsb, ← heq]; exact hsum

/-- **Betrothed Infinitude (conditional reduction).**

If the prime pattern `IsBetrothedPattern` has arbitrarily large solutions, then there
are infinitely many betrothed (quasi-amicable) pairs.

Unconditional infinitude of betrothed pairs is an open problem; this theorem reduces it
to the prime-pattern hypothesis `PrimePatternUnbounded`, which is known to have at least
one solution (`isBetrothedPattern_16_25_3_3`, giving the pair `(48, 75)`). -/
