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

theorem gPair_sound {k n : ℕ} (h : gPair k n = true) : GoldbachPair n := by
  simp only [gPair, List.any_eq_true, Bool.and_eq_true] at h
  obtain ⟨p, -, hp, hq⟩ := h
  have hp' : p.Prime := primeCert_sound hp
  have hq' : (n - p).Prime := primeCert_sound hq
  refine ⟨p, n - p, hp', hq', ?_⟩
  have := hq'.two_le
  omega

/-- `allBelow f M = true` iff `f m = true` for all `m < M`. -/
