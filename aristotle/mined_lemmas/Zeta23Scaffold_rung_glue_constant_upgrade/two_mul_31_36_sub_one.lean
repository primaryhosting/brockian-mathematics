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
# Rung Glue Constant Upgrade
Category: A Assembly
Target: Zeta23Scaffold.rung_glue_constant_upgrade
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

set_option autoImplicit false

namespace Zeta23Scaffold

/-- Constant bookkeeping: `2 * (31/36) - 1 = 13/18`. -/

lemma two_mul_31_36_sub_one : (2 : ℝ) * (31 / 36) - 1 = 13 / 18 := by norm_num

/-- Step (a): the `(2*(31/36) - 1 - eps)`-bound is literally the `(13/18 - eps)`-bound. -/
