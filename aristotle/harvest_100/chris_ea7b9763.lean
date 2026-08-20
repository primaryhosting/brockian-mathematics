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
theorem rung1318_of_bridge (n s : ℝ → ℝ)
    (H : EventualRung n s (2 * (31 / 36) - 1)) :
    EventualRung n s (13 / 18) := by
  have hc : (2 : ℝ) * (31 / 36) - 1 = 13 / 18 := by norm_num
  rwa [hc] at H

/-- Monotonicity of the rung predicate in the constant, for nonnegative `n`. -/
theorem rung_mono (n s : ℝ → ℝ) (hn : ∀ T, 0 ≤ n T) {c c' : ℝ} (hcc : c' ≤ c)
    (H : EventualRung n s c) : EventualRung n s c' := by
  intro eps heps
  obtain ⟨T0, hT0⟩ := H eps heps
  refine ⟨T0, fun T hT => le_trans ?_ (hT0 T hT)⟩
  exact mul_le_mul_of_nonneg_right (by linarith) (hn T)

/-- Part (b): the `13/18` bound dominates the `2/3` bound. -/
theorem rung1318_implies_two_thirds (n s : ℝ → ℝ) (hn : ∀ T, 0 ≤ n T)
    (H : EventualRung n s (13 / 18)) :
    EventualRung n s (2 / 3) :=
  rung_mono n s hn (by norm_num) H

/-- **Rung glue constant upgrade.**  For any nonnegative comparison sequence `n`,
the `(2*(31/36) - 1 - eps)`-bound is exactly the `(13/18 - eps)`-bound, and it
dominates the `(2/3 - eps)`-bound. -/
theorem rung_glue_constant_upgrade (n s : ℝ → ℝ) (hn : ∀ T, 0 ≤ n T)
    (H : ∀ eps > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0,
      (2 * (31 / 36) - 1 - eps) * n T ≤ s T) :
    (∀ eps > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0, (13 / 18 - eps) * n T ≤ s T) ∧
      (∀ eps > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0, (2 / 3 - eps) * n T ≤ s T) := by
  have h1318 : EventualRung n s (13 / 18) := rung1318_of_bridge n s H
  exact ⟨h1318, rung1318_implies_two_thirds n s hn h1318⟩

end Zeta23Scaffold

