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
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean requires `import` to precede any module docstring, so the required header
-- comment appears both at the very top of the file (as a plain comment) and, verbatim,
-- as the module docstring just above.

namespace Brockian.PolignacPrimes

open Nat

/-- `PolignacPair p n` says that `p` and `p + n` are *consecutive* primes:
both are prime and no number strictly between them is prime. -/

lemma polignacPair_three_two : PolignacPair 3 2 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro r h1 h2
  interval_cases r
  · norm_num

/-- Under Dickson's conjecture for pairs of linear forms, there are infinitely many
twin prime pairs. -/
