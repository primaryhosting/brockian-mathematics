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
# Gilbreath Conjecture
Category: Brockian Conjecture
Target: Brockian.GilbreathConjecture.GilbreathConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.GilbreathConjecture

/-- Absolute difference of two natural numbers, written without `Int`. -/

theorem adist_of_mem_pair {a b : ℕ} (ha : a = 0 ∨ a = 2) (hb : b = 0 ∨ b = 2) :
    adist a b = 0 ∨ adist a b = 2 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [adist]

