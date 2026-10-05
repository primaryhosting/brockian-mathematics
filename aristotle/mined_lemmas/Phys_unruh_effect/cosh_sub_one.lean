/-
# Unruh Effect
Category: Frontier Phys
Target: Phys.unruh_effect
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the mandated
-- header above is written as an ordinary block comment; its text is unchanged.)

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

namespace Phys

/-! ## Definitions -/

/-- The **Unruh temperature** `T = ℏ a / (2 π c k_B)` associated with proper acceleration `a`. -/

lemma cosh_sub_one (x : ℝ) : Real.cosh x - 1 = 2 * Real.sinh (x / 2) ^ 2 := by
  have h : Real.cosh x
      = Real.cosh (x / 2) * Real.cosh (x / 2) + Real.sinh (x / 2) * Real.sinh (x / 2) := by
    rw [← Real.cosh_add]; ring_nf
  nlinarith [Real.cosh_sq_sub_sinh_sq (x / 2)]

/-- The Minkowski interval between two points of the uniformly accelerated worldline depends
only on the proper-time difference, through `sinh²(a Δτ / 2c)`. -/
