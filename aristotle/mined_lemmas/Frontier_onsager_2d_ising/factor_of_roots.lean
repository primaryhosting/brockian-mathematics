/-
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
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

/-! ## The 2D Ising model on a finite torus -/

/-- The real value `±1` of a spin encoded as a `Bool`. -/

theorem factor_of_roots (a b c z r r' : ℂ) (hb : b ≠ 0) (hz : z ≠ 0) (hzc : z + z⁻¹ = 2 * c)
    (h1 : r * r' = 1) (h2 : r + r' = 2 * a / b) :
    a - b * c = -(b / 2) * z⁻¹ * (z - r) * (z - r') := by
  have hzi : z⁻¹ * z = 1 := inv_mul_cancel₀ hz
  have hexp : -(b / 2) * z⁻¹ * (z - r) * (z - r')
      = -(b / 2) * (z + z⁻¹) + (b / 2) * (r + r') := by
    linear_combination (-(b / 2) * z + (b / 2) * (r + r')) * hzi + (-(b / 2) * z⁻¹) * h1
  rw [hexp, hzc, h2]
  field_simp
  ring

/-- Pointwise factorisation of `a - b cos θ` as a product of two distances on the unit
circle. -/
