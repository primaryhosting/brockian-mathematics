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
# Andrica Conjecture
Category: Brockian Conjecture
Target: Brockian.AndricaConjecture.AndricaConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Andrica Conjecture
Category: Brockian Conjecture
Target: Brockian.AndricaConjecture.AndricaConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Lean requires `import` commands to precede every other command, including module
docstrings, so the mandated header appears at the top of the file as a plain block
comment and is repeated here as the module docstring.
-/

namespace Brockian.AndricaConjecture

open Real

/-- `prime n` is the `n`-th prime number (`prime 0 = 2`). -/

lemma prime_lt_prime_succ (n : ℕ) : prime n < prime (n + 1) :=
  (Nat.nth_lt_nth Nat.infinite_setOf_prime).mpr (Nat.lt_succ_self n)

/-- The statement of the Andrica conjecture: for every `n`,
`√(p_{n+1}) - √(p_n) < 1`, where `p_n` is the `n`-th prime. -/
