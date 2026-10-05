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

def EventualBound (c : ℝ) (n s : ℝ → ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ T0 : ℝ, ∀ T : ℝ, T0 ≤ T → (c - eps) * n T ≤ s T

/-- Monotonicity of the eventual bound in the constant `c`, for nonnegative `n`. -/
