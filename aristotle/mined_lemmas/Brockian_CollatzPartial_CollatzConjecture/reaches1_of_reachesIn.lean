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
# Collatz Conjecture
Category: Brockian Conjecture
Target: Brockian.CollatzPartial.CollatzConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.CollatzPartial

/-- One step of the Collatz map: `n ↦ n / 2` if `n` is even, `n ↦ 3 * n + 1` if `n` is odd. -/

lemma reaches1_of_reachesIn : ∀ (f n : ℕ), reachesIn f n = true → Reaches1 n := by
  intro f
  induction f with
  | zero =>
      intro n h
      exact ⟨0, by simpa using (by simpa [reachesIn] using h : n = 1)⟩
  | succ f ih =>
      intro n h
      rw [reachesIn, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with h | h
      · exact ⟨0, by simpa using h⟩
      · exact reaches1_of_iterate 1 (by simpa using ih (step n) h)

set_option maxRecDepth 40000 in
