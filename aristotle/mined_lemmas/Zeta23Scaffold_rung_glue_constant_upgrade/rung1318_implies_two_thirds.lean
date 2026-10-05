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

theorem rung1318_implies_two_thirds (n s : ℝ → ℝ) (hn : ∀ T, 0 ≤ n T)
    (H : ∀ eps : ℝ, 0 < eps → ∃ T0 : ℝ, ∀ T : ℝ, T0 ≤ T → (13 / 18 - eps) * n T ≤ s T) :
    ∀ eps : ℝ, 0 < eps → ∃ T0 : ℝ, ∀ T : ℝ, T0 ≤ T → (2 / 3 - eps) * n T ≤ s T :=
  eventualBound_mono hn (by norm_num : (2 / 3 : ℝ) ≤ 13 / 18) H

/-- **Rung glue constant upgrade.**
From the `(2 * (31/36) - 1 - eps)`-bound one gets the `(13/18 - eps)`-bound
(the constants are equal), and from the latter the weaker `(2/3 - eps)`-bound,
since `2/3 ≤ 13/18` and `n` is nonnegative. -/
