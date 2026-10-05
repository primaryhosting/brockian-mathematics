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

lemma eq_of_sq_eq {a m : ℕ} (h : a ^ 2 = m ^ 2) : m = a := by
  rcases lt_trichotomy m a with hlt | heq | hgt
  · nlinarith
  · exact heq
  · nlinarith

/-! ### The Brocard gap hypothesis -/

/-- **Brocard gap hypothesis.**  For every `n ≥ 21` there is a genuine gap between `n ! + 1`
and the perfect squares, i.e. `n ! + 1` is never a perfect square.  This is the open part of
Brocard's problem: the range `8 ≤ n ≤ 20` is settled unconditionally below, so only `n ≥ 21`
needs to be assumed. -/
