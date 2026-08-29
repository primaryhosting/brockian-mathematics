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

/-- Eventual lower bound of `s` by `(c - eps) * n`, for every `eps > 0`. -/

theorem rung1318_of_bridge (n s : ℝ → ℝ)
    (H : ∀ eps : ℝ, 0 < eps → ∃ T0 : ℝ, ∀ T : ℝ, T0 ≤ T →
      (2 * (31 / 36) - 1 - eps) * n T ≤ s T) :
    ∀ eps : ℝ, 0 < eps → ∃ T0 : ℝ, ∀ T : ℝ, T0 ≤ T → (13 / 18 - eps) * n T ≤ s T := by
  intro eps heps
  obtain ⟨T0, hT0⟩ := H eps heps
  refine ⟨T0, fun T hT => ?_⟩
  have h := hT0 T hT
  have : (13 / 18 - eps : ℝ) = 2 * (31 / 36) - 1 - eps := by norm_num
  rw [this]
  exact h

/-- Part (b): the `(13/18 - eps)`-bound implies the `(2/3 - eps)`-bound when `n` is nonnegative. -/
