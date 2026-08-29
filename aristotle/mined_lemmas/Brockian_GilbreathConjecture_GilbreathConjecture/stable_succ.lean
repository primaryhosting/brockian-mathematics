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

theorem stable_succ {n : ℕ} (h : Stable n) : Stable (n + 1) := by
  obtain ⟨h0, h2⟩ := h
  constructor
  · have := h2 1 le_rfl
    simp only [gRow, h0]
    rcases this with h | h <;> simp [adist, h]
  · intro k hk
    exact adist_of_mem_pair (h2 k hk) (h2 (k + 1) (by omega))

