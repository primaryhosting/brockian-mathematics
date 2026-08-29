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

def PolignacPair (p n : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime (p + n) ∧ ∀ r, p < r → r < p + n → ¬ Nat.Prime r

/-- **Dickson's conjecture** for the pair of linear forms `A * x + B` and `A * x + B + n`:
if the pair is admissible (for every prime `q` some value of `x` makes neither form
divisible by `q`), then both forms are simultaneously prime for arbitrarily large `x`. -/
