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

theorem rung1318_iff_bridge (n s : ℝ → ℝ) :
    (∀ eps > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0, (2 * (31 / 36) - 1 - eps) * n T ≤ s T) ↔
      (∀ eps > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0, (13 / 18 - eps) * n T ≤ s T) := by
  rw [two_mul_31_36_sub_one]

/-- **Rung glue constant upgrade.** For any `n s : ℝ → ℝ` with `n` nonnegative:
the eventual `(2*(31/36) - 1 - eps)`-lower bound on `s` in terms of `n`
(a) upgrades to the `(13/18 - eps)`-bound, and (b) that in turn implies the
`(2/3 - eps)`-bound. -/
