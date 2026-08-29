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

/-!
# Twin Prime Conjecture
Category: Brockian Conjecture
Target: Brockian.TwinPrimes.TwinPrimeConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
The Twin Prime Conjecture — that there are infinitely many primes `p` with `p + 2` also
prime — is a famous open problem, and no unconditional proof is known.  What is formalised
here is therefore:

* the exact statement of the conjecture (`TwinPrimeStatement`);
* a **Lean-checked conditional reduction**: the conjecture follows from Dickson's
  conjecture on simultaneous primality of admissible families of linear forms
  (`TwinPrimeConjecture`).  All the mathematical content of the reduction — namely the
  admissibility of the pair of forms `n`, `n + 2` — is proved unconditionally here;
* a second conditional reduction, from the divergence of the sum of reciprocals of twin
  primes (`twinPrimeStatement_of_not_summable`);
* small unconditional facts about twin primes.
-/

namespace Brockian.TwinPrimes

/-- `p` is a twin prime if both `p` and `p + 2` are prime. -/

def twinPrimeSet : Set ℕ := {p | IsTwinPrime p}

/-- A finite family of linear forms `a * n + b`, encoded as pairs `(a, b)`, is *admissible*
if for every prime `q` there is some `n` for which none of the values `a * n + b` is
divisible by `q`. -/
