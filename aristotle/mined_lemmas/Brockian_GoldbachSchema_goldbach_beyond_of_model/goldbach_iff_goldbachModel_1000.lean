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

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian
namespace GoldbachSchema

/-- Goldbach's property at `n`: `n` is a sum of two primes. -/

theorem goldbach_iff_goldbachModel_1000 :
    GoldbachModel 1000 ↔ ∀ n : ℕ, 4 ≤ n → Even n → Goldbach n := by
  constructor
  · intro h
    exact goldbach_beyond_of_model (B := 1000) le_rfl h
  · intro h n hn he
    exact h n (by omega) he

end GoldbachSchema
end Brockian

