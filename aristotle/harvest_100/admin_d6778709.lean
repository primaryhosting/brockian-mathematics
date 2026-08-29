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

/-- Part (a): the `2*(31/36) - 1` eventual bound is the `13/18` eventual bound,
since `2*(31/36) - 1 = 13/18`. -/
theorem rung1318_of_bridge (n s : Real → Real)
    (H : ∀ eps > (0 : Real), ∃ T0 : Real, ∀ T ≥ T0, (2 * (31 / 36) - 1 - eps) * n T ≤ s T) :
    ∀ eps > (0 : Real), ∃ T0 : Real, ∀ T ≥ T0, (13 / 18 - eps) * n T ≤ s T := by
  intro eps heps
  obtain ⟨T0, hT0⟩ := H eps heps
  refine ⟨T0, fun T hT => ?_⟩
  have h := hT0 T hT
  have : (2 * (31 / 36) - 1 - eps) = (13 / 18 - eps : Real) := by norm_num
  rwa [this] at h

/-- Part (b): the `13/18` eventual bound implies the `2/3` eventual bound,
using `2/3 ≤ 13/18` and nonnegativity of `n`. -/
theorem rung1318_implies_two_thirds (n s : Real → Real) (hn : ∀ T : Real, 0 ≤ n T)
    (H : ∀ eps > (0 : Real), ∃ T0 : Real, ∀ T ≥ T0, (13 / 18 - eps) * n T ≤ s T) :
    ∀ eps > (0 : Real), ∃ T0 : Real, ∀ T ≥ T0, (2 / 3 - eps) * n T ≤ s T := by
  intro eps heps
  obtain ⟨T0, hT0⟩ := H eps heps
  refine ⟨T0, fun T hT => ?_⟩
  have h := hT0 T hT
  have hmono : (2 / 3 - eps) * n T ≤ (13 / 18 - eps) * n T := by
    nlinarith [hn T]
  linarith

/-- Abstract rung glue: the `(2*(31/36) - 1 - eps)`-bound equals the `(13/18 - eps)`-bound
and dominates the `(2/3 - eps)`-bound, for any nonnegative comparison sequence `n`. -/
theorem rung_glue_constant_upgrade (n s : Real → Real) (hn : ∀ T : Real, 0 ≤ n T)
    (H : ∀ eps > (0 : Real), ∃ T0 : Real, ∀ T ≥ T0, (2 * (31 / 36) - 1 - eps) * n T ≤ s T) :
    (∀ eps > (0 : Real), ∃ T0 : Real, ∀ T ≥ T0, (13 / 18 - eps) * n T ≤ s T) ∧
      (∀ eps > (0 : Real), ∃ T0 : Real, ∀ T ≥ T0, (2 / 3 - eps) * n T ≤ s T) := by
  have h1 := rung1318_of_bridge n s H
  exact ⟨h1, rung1318_implies_two_thirds n s hn h1⟩

end Zeta23Scaffold

