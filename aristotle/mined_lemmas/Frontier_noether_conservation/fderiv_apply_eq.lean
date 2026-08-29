/-
# Noether Conservation
Category: Frontier Physics
Target: Frontier.noether_conservation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Noether Conservation
Category: Frontier Physics
Target: Frontier.noether_conservation
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

namespace Frontier

/-- The partial derivative `∂L/∂q` of a one–dimensional Lagrangian
`L : ℝ × ℝ → ℝ` (first slot: position, second slot: velocity). -/

lemma fderiv_apply_eq (L : ℝ × ℝ → ℝ) (x v a b : ℝ) :
    fderiv ℝ L (x, v) (a, b) = a * Lpos L x v + b * Lvel L x v := by
  have h : ((a, b) : ℝ × ℝ) = a • ((1, 0) : ℝ × ℝ) + b • ((0, 1) : ℝ × ℝ) := by
    simp
  rw [h, map_add, map_smul, map_smul]
  simp [Lpos, Lvel, smul_eq_mul]

/-- **Infinitesimal invariance implies the Noether identity.**
If `L` is invariant to first order under the flow `q ↦ q + s X(q)` (with the induced
action `v ↦ v + s X'(q) v` on velocities), then the pointwise Noether identity
`(∂L/∂q) X + (∂L/∂q̇) X' v = 0` holds. -/
