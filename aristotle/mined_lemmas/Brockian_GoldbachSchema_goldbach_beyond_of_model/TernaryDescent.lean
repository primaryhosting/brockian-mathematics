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
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
namespace Brockian
namespace GoldbachSchema

/-- The binary Goldbach property: `n` is a sum of two primes. -/

theorem ternaryDescent : TernaryDescent := by
  rintro n hodd h3 ⟨p, q, hp, hq, hpq⟩
  exact ⟨3, p, q, Nat.prime_three, hp, hq, by omega⟩

/-- **Goldbach beyond, of a model** (unconditional in the named hypothesis).

Given any model `M` of binary Goldbach beyond `M.bound`, every number `n ≥ M.bound + 3` satisfies
the Goldbach property appropriate to its parity: an even such `n` is a sum of two primes, and an
odd such `n` is a sum of three primes.

The auxiliary hypothesis `TernaryDescent`, relative to which the schema is stated, has been
discharged (see `ternaryDescent`), so the result depends only on the model. -/
