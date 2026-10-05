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

theorem eventualBound_mono {c c' : ℝ} {n s : ℝ → ℝ} (hn : ∀ T, 0 ≤ n T)
    (hcc : c' ≤ c) (h : EventualBound c n s) : EventualBound c' n s := by
  intro eps heps
  obtain ⟨T0, hT0⟩ := h eps heps
  refine ⟨T0, fun T hT => le_trans ?_ (hT0 T hT)⟩
  have : c' - eps ≤ c - eps := by linarith
  exact mul_le_mul_of_nonneg_right this (hn T)

/-- Part (a): the `(2 * (31/36) - 1 - eps)`-bound is literally the `(13/18 - eps)`-bound. -/
