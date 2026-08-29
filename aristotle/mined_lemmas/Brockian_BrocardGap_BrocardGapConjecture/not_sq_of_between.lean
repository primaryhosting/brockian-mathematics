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
# Brocard Gap Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardGap.BrocardGapConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Nat

namespace Brockian.BrocardGap

/-! ### Elementary facts about perfect squares -/

/-- If `k` lies strictly between two consecutive squares, it is not a square. -/

lemma not_sq_of_between {k a : ℕ} (h1 : a ^ 2 < k) (h2 : k < (a + 1) ^ 2) (m : ℕ) :
    k ≠ m ^ 2 := by
  rintro rfl
  have hlt : a < m := by
    by_contra h
    push_neg at h
    nlinarith
  have hgt : m < a + 1 := by
    by_contra h
    push_neg at h
    nlinarith
  omega

/-- Squares determine their (natural number) roots. -/
