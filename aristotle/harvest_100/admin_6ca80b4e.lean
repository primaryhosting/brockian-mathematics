/-
# Rung Glue Constant Upgrade
Category: A Assembly
Target: Zeta23Scaffold.rung_glue_constant_upgrade
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Zeta23Scaffold

/-- Part (a): the eventual bound with constant `2*(31/36) - 1` is literally the bound with
constant `13/18`, since `2*(31/36) - 1 = 13/18`. -/
theorem rung1318_of_bridge_seq (n s : ℝ → ℝ)
    (H : ∀ eps > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0, (2 * (31 / 36) - 1 - eps) * n T ≤ s T) :
    ∀ eps > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0, (13 / 18 - eps) * n T ≤ s T := by
  intro eps heps
  obtain ⟨T0, hT0⟩ := H eps heps
  refine ⟨T0, fun T hT => ?_⟩
  have := hT0 T hT
  norm_num at this ⊢
  linarith

/-- Part (b): the `13/18 - eps` bound dominates the `2/3 - eps` bound, for a nonnegative
comparison sequence `n`. -/
theorem rung1318_implies_two_thirds_seq (n s : ℝ → ℝ) (hn : ∀ T, 0 ≤ n T)
    (H : ∀ eps > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0, (13 / 18 - eps) * n T ≤ s T) :
    ∀ eps > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0, (2 / 3 - eps) * n T ≤ s T := by
  intro eps heps
  obtain ⟨T0, hT0⟩ := H eps heps
  refine ⟨T0, fun T hT => ?_⟩
  have h := hT0 T hT
  have hmono : (2 / 3 - eps) * n T ≤ (13 / 18 - eps) * n T := by
    have : (2 / 3 - eps) ≤ (13 / 18 - eps) := by norm_num
    exact mul_le_mul_of_nonneg_right this (hn T)
  linarith

/-- Abstract rung glue, unconditional in the sense that the `2*(31/36) - 1 - eps` hypothesis is
discharged into both conclusions: it yields the `13/18 - eps` bound (part (a)), which in turn
dominates the `2/3 - eps` bound (part (b)). -/
theorem rung_glue_constant_upgrade (n s : ℝ → ℝ) (hn : ∀ T, 0 ≤ n T)
    (H : ∀ eps > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0, (2 * (31 / 36) - 1 - eps) * n T ≤ s T) :
    (∀ eps > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0, (13 / 18 - eps) * n T ≤ s T) ∧
      (∀ eps > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0, (2 / 3 - eps) * n T ≤ s T) := by
  have ha := rung1318_of_bridge_seq n s H
  exact ⟨ha, rung1318_implies_two_thirds_seq n s hn ha⟩

end Zeta23Scaffold

