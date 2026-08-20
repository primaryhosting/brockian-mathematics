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

theorem isBetrothedPair_140_195 : IsBetrothedPair 140 195 := by
  refine ⟨by norm_num, ?_, ?_⟩ <;> rw [sigma_one_apply] <;> decide

set_option maxRecDepth 20000 in
/-- `(1050, 1925)` is a betrothed pair. -/
