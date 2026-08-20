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
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.GoldbachSchema

/-- `GoldbachBeyond N` says that *beyond* the bound `N` there is an even number which is a
sum of two distinct primes, i.e. the Goldbach representation property is witnessed at some
even number larger than `N`. -/

theorem bertrandModel_holds : BertrandModel :=
  Nat.exists_prime_lt_and_le_two_mul

/-- **Goldbach beyond, unconditional.**  For every bound `N` there is an even number `m > N`
which is the sum of two distinct primes.  The model hypothesis of the schema has been
discharged via Bertrand's postulate (`Nat.exists_prime_lt_and_le_two_mul`). -/
