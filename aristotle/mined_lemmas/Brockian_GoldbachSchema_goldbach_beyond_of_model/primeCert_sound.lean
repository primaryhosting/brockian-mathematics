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

theorem primeCert_sound {k n : ℕ} (h : primeCert k n = true) : n.Prime := by
  simp only [primeCert, Bool.and_eq_true, decide_eq_true_eq, noDiv_iff] at h
  obtain ⟨⟨h2, hlt⟩, hnd⟩ := h
  refine Nat.prime_def_le_sqrt.mpr ⟨h2, fun m hm hms => hnd m hm ?_⟩
  have h1 : Nat.sqrt n < k + 1 := Nat.sqrt_lt'.mpr (by simpa [pow_two] using hlt)
  have h2' : Nat.sqrt n < n := Nat.sqrt_lt_self (by omega)
  omega

/-! ## The verified finite model -/

/-- The small primes used as the first summand of the Goldbach representations. -/
