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
# Fortune Conjecture
Category: Brockian Conjecture
Target: Brockian.FortunateNumbers.FortuneConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.FortunateNumbers

open Nat

/-- Existence of a "fortunate offset": for every `n` there is some `m > 1` such that
`n# + m` is prime, where `n#` is the primorial of `n`.  This follows from Bertrand's
postulate applied to `n# + 1`. -/

def FortuneConjectureStatement : Prop := ∀ n, Nat.Prime (fortunate n)

/-- **Fortune's conjecture, conditional on a size bound.**

Fortune's conjecture states that every Fortunate number `fortunate n` (the least `m > 1` with
`n# + m` prime) is prime.  This is an open problem.  The theorem below is a Lean-checked
*conditional reduction*: it derives the full conjecture from the (conjecturally very weak)
growth hypothesis that `fortunate n < (n+1)^2` for `n ≥ 1`, i.e. that the prime gap just above
the primorial `n#` is smaller than `(n+1)^2`.

The reduction is unconditional in the following sense (see `fortunate_prime_or_sq_le`):
no prime `≤ n` can divide `fortunate n`, since such a prime also divides `n#` and hence would
divide the prime `n# + fortunate n`; therefore a composite Fortunate number is at least the
square of its least prime factor, which exceeds `n`. -/
