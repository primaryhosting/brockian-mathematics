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
# Triangular Mod 5 Mem
Category: Cone Line
Target: Brockian.ConeLine.triangular_mod5_mem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.ConeLine

/-- The `n`-th triangular number, `T n = n(n+1)/2` (natural-number division). -/

lemma T_small_mem (r : ℕ) (hr : r < 10) :
    ((T r : ℕ) : ZMod 5) ∈ ({0, 1, 3} : Set (ZMod 5)) := by
  unfold T
  interval_cases r <;> norm_num <;> decide

/-- Triangular numbers only hit residues `0`, `1`, `3` modulo `5`. -/
