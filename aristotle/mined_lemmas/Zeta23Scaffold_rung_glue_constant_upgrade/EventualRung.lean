import Mathlib

/-!
# Rung Glue Constant Upgrade
Category: A Assembly
Target: Zeta23Scaffold.rung_glue_constant_upgrade
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Zeta23Scaffold

/-- Abstract rung predicate: eventually, `(c - eps) * n T ≤ s T` for every `eps > 0`. -/

def EventualRung (n s : ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ eps > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0, (c - eps) * n T ≤ s T

/-- Part (a): the `2*(31/36) - 1` bound *is* the `13/18` bound, since
`2*(31/36) - 1 = 13/18`. -/
