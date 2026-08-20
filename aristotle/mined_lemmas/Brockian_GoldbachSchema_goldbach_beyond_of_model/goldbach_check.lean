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

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Brockian.GoldbachSchema

/-- The bound up to which the binary Goldbach property is verified here by kernel
computation (`decide`). -/

private lemma goldbach_check :
    ∀ n ∈ Finset.range (verifiedBound + 1), 4 ≤ n → Even n →
      ∃ p ∈ Finset.range (n + 1), Nat.Prime p ∧ Nat.Prime (n - p) := by
  decide

/-- Every even number `n` with `4 ≤ n ≤ verifiedBound` is a sum of two primes. -/
