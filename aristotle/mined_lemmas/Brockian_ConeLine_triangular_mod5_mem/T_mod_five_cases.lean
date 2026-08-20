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

import Mathlib

/-!
# Triangular Mod 5 Mem
Category: Cone Line
Target: Brockian.ConeLine.triangular_mod5_mem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ConeLine

/-- The `n`-th triangular number, computed in `ℕ` (division after multiplication). -/

lemma T_mod_five_cases (n : ℕ) : T n % 5 = 0 ∨ T n % 5 = 1 ∨ T n % 5 = 3 := by
  rw [T_mod_five_periodic n]
  have hr : n % 10 < 10 := Nat.mod_lt _ (by norm_num)
  interval_cases h : (n % 10) <;> simp [T]

/-- Triangular numbers only ever land on the residues `0`, `1`, `3` mod 5. -/
