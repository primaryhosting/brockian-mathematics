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
theorem rung1318_of_bridge (n s : ℝ → ℝ)
    (H : ∀ eps > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0, (2 * (31 / 36) - 1 - eps) * n T ≤ s T) :
    ∀ eps > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0, (13 / 18 - eps) * n T ≤ s T := by
  intro eps heps
  obtain ⟨T0, hT0⟩ := H eps heps
  refine ⟨T0, fun T hT => ?_⟩
  have := hT0 T hT
  rwa [two_mul_31_36_sub_one] at this

/-- Step (b): the `(13/18 - eps)`-bound dominates the `(2/3 - eps)`-bound, for a
nonnegative comparison sequence `n`. -/
theorem rung1318_implies_two_thirds (n s : ℝ → ℝ) (hn : ∀ T, 0 ≤ n T)
    (H : ∀ eps > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0, (13 / 18 - eps) * n T ≤ s T) :
    ∀ eps > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0, (2 / 3 - eps) * n T ≤ s T := by
  intro eps heps
  obtain ⟨T0, hT0⟩ := H eps heps
  refine ⟨T0, fun T hT => ?_⟩
  refine le_trans ?_ (hT0 T hT)
  have hle : (2 : ℝ) / 3 - eps ≤ 13 / 18 - eps := by norm_num
  exact mul_le_mul_of_nonneg_right hle (hn T)

/-- Step (a), sharpened: since `2*(31/36) - 1 = 13/18`, the two eventual bounds are
equivalent, not merely related by implication. -/
theorem rung1318_iff_bridge (n s : ℝ → ℝ) :
    (∀ eps > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0, (2 * (31 / 36) - 1 - eps) * n T ≤ s T) ↔
      (∀ eps > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0, (13 / 18 - eps) * n T ≤ s T) := by
  rw [two_mul_31_36_sub_one]

/-- **Rung glue constant upgrade.** For any `n s : ℝ → ℝ` with `n` nonnegative:
the eventual `(2*(31/36) - 1 - eps)`-lower bound on `s` in terms of `n`
(a) upgrades to the `(13/18 - eps)`-bound, and (b) that in turn implies the
`(2/3 - eps)`-bound. -/
theorem rung_glue_constant_upgrade (n s : ℝ → ℝ) (hn : ∀ T, 0 ≤ n T) :
    ((∀ eps > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0, (2 * (31 / 36) - 1 - eps) * n T ≤ s T) →
      (∀ eps > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0, (13 / 18 - eps) * n T ≤ s T)) ∧
    ((∀ eps > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0, (13 / 18 - eps) * n T ≤ s T) →
      (∀ eps > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0, (2 / 3 - eps) * n T ≤ s T)) :=
  ⟨rung1318_of_bridge n s, rung1318_implies_two_thirds n s hn⟩

end Zeta23Scaffold

