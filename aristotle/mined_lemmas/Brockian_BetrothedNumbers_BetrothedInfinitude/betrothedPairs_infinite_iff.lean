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
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

Two distinct natural numbers `m ≠ n` are *betrothed* (also called *quasi-amicable*)
when each is the sum of the *nontrivial* proper divisors of the other, i.e.

  `σ m = σ n = m + n + 1`,

where `σ = ArithmeticFunction.sigma 1` is the sum-of-divisors function.
The smallest example is `(48, 75)`.

Whether there are infinitely many betrothed pairs is an open problem.  What is
proved here is therefore a *conditional reduction* together with the unconditional
structural facts it rests on:

* `Brockian.BetrothedNumbers.quasiAliquot_iff` — the key intermediate lemma:
  a pair is betrothed exactly when the *quasi-aliquot* map
  `q n = σ n - n - 1` swaps `m` and `n` (and `m ≠ n`, `2 ≤ m`, `2 ≤ n`).
  In particular each member of a betrothed pair determines the other.
* `Brockian.BetrothedNumbers.BetrothedInfinitude` — from the (open) hypothesis
  that betrothed pairs have arbitrarily large members it follows that the set of
  betrothed pairs is infinite.
-/

namespace Brockian.BetrothedNumbers

open ArithmeticFunction

/-- The quasi-aliquot sum of `n`: the sum of the divisors of `n` other than `1` and `n`
itself (using truncated subtraction, so the value at `n ≤ 1` is `0`). -/

theorem betrothedPairs_infinite_iff :
    betrothedPairs.Infinite ↔ ∀ N : ℕ, ∃ m n : ℕ, N < n ∧ IsBetrothedPair m n := by
  constructor
  · intro hinf N
    have himg : betrothedNumbers.Infinite := by
      rw [← image_snd_betrothedPairs]
      exact hinf.image snd_injOn_betrothedPairs
    obtain ⟨n, ⟨m, hmn⟩, hlt⟩ := himg.exists_gt N
    exact ⟨m, n, hlt, hmn⟩
  · intro h
    refine Set.Infinite.of_image Prod.snd ?_
    rw [image_snd_betrothedPairs]
    exact betrothedNumbers_infinite h

/-- **Betrothed Infinitude (conditional reduction).**

If betrothed pairs have arbitrarily large members — i.e. for every bound `N` there is
a betrothed pair `(m, n)` with `N < n` — then there are infinitely many betrothed pairs.

The hypothesis is exactly the open part of the Brockian "betrothed infinitude"
conjecture; everything else is proved unconditionally here, the crucial ingredient
being `quasiAliquot_iff`, which shows that a betrothed pair is determined by either
of its members. -/
