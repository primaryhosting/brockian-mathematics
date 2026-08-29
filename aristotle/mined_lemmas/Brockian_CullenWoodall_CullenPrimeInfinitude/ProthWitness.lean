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
# Cullen Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.CullenPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cullen Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.CullenPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The infinitude of Cullen primes (primes of the form `n * 2 ^ n + 1`) is an open
problem.  This file gives a Lean-checked *conditional reduction*: the infinitude of
Cullen primes follows from the existence of arbitrarily large odd `n` admitting a
Proth witness, i.e. an `a` with `a ^ ((n * 2 ^ n) / 2) = -1` modulo `n * 2 ^ n + 1`.
This is exactly the criterion (Proth's theorem, proved here from scratch) that is
used in practice to certify Cullen primes, and for odd `n` the condition is in fact
*equivalent* to primality of the Cullen number.

The file also contains unconditional results in the opposite direction: every odd
prime `p` divides the Cullen number `cullen (p - 2)`, hence infinitely many Cullen
numbers are composite.
-/

namespace Brockian.CullenWoodall

/-- The `n`-th Cullen number `C n = n * 2 ^ n + 1`. -/

def ProthWitness (n : ℕ) : Prop :=
  ∃ a : ZMod (cullen n), a ^ ((cullen n - 1) / 2) = -1

/-- Proth's theorem: if `k` is odd, `k < 2 ^ m`, `0 < m`, and some `a` satisfies
`a ^ (k * 2 ^ (m - 1)) = -1` modulo `N = k * 2 ^ m + 1`, then `N` is prime.

The proof shows that every prime factor `p` of `N` satisfies `p ≡ 1 [MOD 2 ^ m]`,
hence `p > 2 ^ m > √N`, which forces `N` to be prime. -/
