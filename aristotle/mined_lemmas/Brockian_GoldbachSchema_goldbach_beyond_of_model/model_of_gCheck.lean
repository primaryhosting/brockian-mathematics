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

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.GoldbachSchema

/-! ## The statements -/

/-- `GoldbachPair n` : `n` is a sum of two primes. -/

theorem model_of_gCheck {k M : ℕ} (h : gCheck k M = true) : GoldbachModel (2 * M + 2) := by
  intro n h4 hle heven
  obtain ⟨t, ht⟩ := heven
  have hm : n = 2 * (t - 2) + 4 := by omega
  have hlt : t - 2 < M := by omega
  rw [hm]
  exact gPair_sound (allBelow_sound (f := fun m => gPair k (2 * m + 4)) h hlt)

/-- The binary Goldbach property, verified by kernel computation for every even number
between `4` and `2002`. -/
