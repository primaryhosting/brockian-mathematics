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

theorem rung_mono (n s : ℝ → ℝ) (hn : ∀ T, 0 ≤ n T) {c c' : ℝ} (hcc : c' ≤ c)
    (H : EventualRung n s c) : EventualRung n s c' := by
  intro eps heps
  obtain ⟨T0, hT0⟩ := H eps heps
  refine ⟨T0, fun T hT => le_trans ?_ (hT0 T hT)⟩
  exact mul_le_mul_of_nonneg_right (by linarith) (hn T)

/-- Part (b): the `13/18` bound dominates the `2/3` bound. -/
