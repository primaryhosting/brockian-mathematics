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

/-- **Rung glue, step (a).** The eventual bound with constant `2 * (31/36) - 1`
upgrades (in fact, *is*) the eventual bound with constant `13/18`. -/
theorem rung1318_of_bridge (n s : ℝ → ℝ)
    (H : ∀ eps > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0, (2 * (31 / 36) - 1 - eps) * n T ≤ s T) :
    ∀ eps > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0, (13 / 18 - eps) * n T ≤ s T := by
  intro eps heps
  obtain ⟨T0, hT0⟩ := H eps heps
  refine ⟨T0, fun T hT => ?_⟩
  have h := hT0 T hT
  have hc : (2 * (31 / 36) - 1 - eps : ℝ) = 13 / 18 - eps := by norm_num
  rwa [hc] at h

/-- **Rung glue, step (b).** Since `2/3 ≤ 13/18` and the comparison sequence `n`
is nonnegative, the `13/18`-bound dominates the `2/3`-bound. -/
theorem rung1318_implies_two_thirds (n s : ℝ → ℝ) (hn : ∀ T, 0 ≤ n T)
    (H : ∀ eps > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0, (13 / 18 - eps) * n T ≤ s T) :
    ∀ eps > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0, (2 / 3 - eps) * n T ≤ s T := by
  intro eps heps
  obtain ⟨T0, hT0⟩ := H eps heps
  refine ⟨T0, fun T hT => ?_⟩
  have h1 := hT0 T hT
  have h2 : (2 / 3 - eps) * n T ≤ (13 / 18 - eps) * n T := by
    nlinarith [hn T]
  linarith

/-- **Rung glue constant upgrade.** For any nonnegative comparison sequence `n`
and any `s`, an eventual lower bound with constant `2 * (31/36) - 1` yields both
the `13/18`-bound (part (a): the constants are equal) and the `2/3`-bound
(part (b): `2/3 ≤ 13/18` together with `n ≥ 0`). -/
theorem rung_glue_constant_upgrade (n s : ℝ → ℝ) (hn : ∀ T, 0 ≤ n T)
    (H : ∀ eps > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0, (2 * (31 / 36) - 1 - eps) * n T ≤ s T) :
    (∀ eps > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0, (13 / 18 - eps) * n T ≤ s T) ∧
      (∀ eps > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0, (2 / 3 - eps) * n T ≤ s T) := by
  have ha := rung1318_of_bridge n s H
  exact ⟨ha, rung1318_implies_two_thirds n s hn ha⟩

end Zeta23Scaffold

