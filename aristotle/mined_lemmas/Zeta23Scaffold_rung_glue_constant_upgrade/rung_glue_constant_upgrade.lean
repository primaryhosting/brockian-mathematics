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

import Mathlib

/-!
# Rung Glue Constant Upgrade
Category: A Assembly
Target: Zeta23Scaffold.rung_glue_constant_upgrade
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


set_option autoImplicit false

namespace Zeta23Scaffold

/-- **Rung glue: constant upgrade.**

Abstract sequence form of the glue steps `rung1318_of_bridge` and
`rung1318_implies_two_thirds`.  Let `n s : ℝ → ℝ` with `n` nonnegative.

(a) If for every `eps > 0` the bound `(2*(31/36) - 1 - eps) * n T ≤ s T` holds for
all sufficiently large `T`, then the same holds with the constant `13/18`
(indeed `2*(31/36) - 1 = 13/18`).

(b) That conclusion in turn implies the corresponding statement with `2/3` in
place of `13/18`, since `2/3 ≤ 13/18` and `n T ≥ 0`. -/

theorem rung_glue_constant_upgrade (n s : Real → Real) (hn : ∀ T : Real, 0 ≤ n T)
    (H : ∀ eps : Real, 0 < eps → ∃ T0 : Real, ∀ T : Real, T0 ≤ T →
      (2 * (31 / 36) - 1 - eps) * n T ≤ s T) :
    (∀ eps : Real, 0 < eps → ∃ T0 : Real, ∀ T : Real, T0 ≤ T →
      (13 / 18 - eps) * n T ≤ s T) ∧
    (∀ eps : Real, 0 < eps → ∃ T0 : Real, ∀ T : Real, T0 ≤ T →
      (2 / 3 - eps) * n T ≤ s T) := by
  have ha : ∀ eps : Real, 0 < eps → ∃ T0 : Real, ∀ T : Real, T0 ≤ T →
      (13 / 18 - eps) * n T ≤ s T := by
    intro eps heps
    obtain ⟨T0, hT0⟩ := H eps heps
    refine ⟨T0, fun T hT => ?_⟩
    have hb := hT0 T hT
    have hc : (2 * (31 / 36) - 1 - eps : Real) = 13 / 18 - eps := by norm_num
    rwa [hc] at hb
  refine ⟨ha, fun eps heps => ?_⟩
  obtain ⟨T0, hT0⟩ := ha eps heps
  refine ⟨T0, fun T hT => le_trans ?_ (hT0 T hT)⟩
  have hle : (2 / 3 - eps : Real) ≤ 13 / 18 - eps := by norm_num
  exact mul_le_mul_of_nonneg_right hle (hn T)

end Zeta23Scaffold

