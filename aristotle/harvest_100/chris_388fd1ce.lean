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

namespace Zeta23Scaffold

/-- Part (a): the `2*(31/36) - 1` bound is literally the `13/18` bound. -/
theorem rung1318_of_bridge (n s : ℝ → ℝ)
    (H : ∀ eps > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0, (2 * (31 / 36) - 1 - eps) * n T ≤ s T) :
    ∀ eps > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0, (13 / 18 - eps) * n T ≤ s T := by
  intro eps heps
  obtain ⟨T0, hT0⟩ := H eps heps
  refine ⟨T0, fun T hT => ?_⟩
  have := hT0 T hT
  norm_num at this ⊢
  linarith [this]

/-- Part (b): the `13/18` bound dominates the `2/3` bound, for a nonnegative sequence `n`. -/
theorem rung1318_implies_two_thirds (n s : ℝ → ℝ) (hn : ∀ T, 0 ≤ n T)
    (H : ∀ eps > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0, (13 / 18 - eps) * n T ≤ s T) :
    ∀ eps > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0, (2 / 3 - eps) * n T ≤ s T := by
  intro eps heps
  obtain ⟨T0, hT0⟩ := H eps heps
  refine ⟨T0, fun T hT => ?_⟩
  have h1 : (2 / 3 - eps) * n T ≤ (13 / 18 - eps) * n T := by
    have : (2 / 3 - eps) ≤ (13 / 18 - eps) := by norm_num
    exact mul_le_mul_of_nonneg_right this (hn T)
  exact h1.trans (hT0 T hT)

/-- Rung glue constant upgrade: from the `2*(31/36) - 1 - eps` bound one obtains both the
`13/18 - eps` bound (an identity of constants) and, using nonnegativity of `n`, the weaker
`2/3 - eps` bound. -/
theorem rung_glue_constant_upgrade (n s : ℝ → ℝ) (hn : ∀ T, 0 ≤ n T)
    (H : ∀ eps > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0, (2 * (31 / 36) - 1 - eps) * n T ≤ s T) :
    (∀ eps > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0, (13 / 18 - eps) * n T ≤ s T) ∧
      (∀ eps > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0, (2 / 3 - eps) * n T ≤ s T) := by
  have ha := rung1318_of_bridge n s H
  exact ⟨ha, rung1318_implies_two_thirds n s hn ha⟩

end Zeta23Scaffold

