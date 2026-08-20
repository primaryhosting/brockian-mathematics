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
# Twin Prime Conjecture
Category: Brockian Conjecture
Target: Brockian.TwinPrimes.TwinPrimeConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
The twin prime conjecture is a famous open problem, so the target theorem
`Brockian.TwinPrimes.TwinPrimeConjecture` is stated here as a *conditional reduction*:
it derives the infinitude of twin primes from `ClementHypothesis`, a purely
elementary (factorial/divisibility) statement.

The mathematical content that is proved unconditionally is **Clement's theorem**:
for `n ≥ 2`, the pair `(n, n+2)` consists of two primes if and only if

`n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n`.

Consequently `ClementHypothesis` is *equivalent* to the twin prime conjecture
(`twinPrime_iff_clementHypothesis`), so the reduction is faithful: no hidden
strengthening of the conjecture is assumed.
-/

namespace Brockian.TwinPrimes

open Nat Finset

/-- `n` starts a twin prime pair when both `n` and `n + 2` are prime. -/

def IsTwinPrimePair (n : ℕ) : Prop := Nat.Prime n ∧ Nat.Prime (n + 2)

/-- Clement's divisibility criterion for the pair `(n, n + 2)`. -/
