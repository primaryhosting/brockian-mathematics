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

theorem allBelow_sound {f : ℕ → Bool} : ∀ {M m : ℕ}, allBelow f M = true → m < M → f m = true := by
  intro M
  induction M with
  | zero => intro m _ hm; omega
  | succ M ih =>
    intro m h hm
    simp only [allBelow, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge m M with hlt | hge
    · exact ih h.2 hlt
    · have hmM : m = M := by omega
      subst hmM
      exact h.1

/-- Boolean check of the binary Goldbach property for all even `n = 2 * m + 4` with `m < M`. -/
