/-
# Hairer KPZ
Category: Frontier — Fields Medal Work
Target: Frontier.hairer_KPZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hairer KPZ
Category: Frontier — Fields Medal Work
Target: Frontier.hairer_KPZ
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

/-! ## Space-time partial derivatives

We work with real functions `f : ℝ → ℝ → ℝ` of a time variable and a (one dimensional)
space variable. -/

/-- Partial derivative in the time variable. -/

theorem dx_dx_log (Z : ℝ → ℝ → ℝ) (hreg : SpaceTimeReg Z) (hpos : ∀ t x : ℝ, 0 < Z t x)
    (t x : ℝ) :
    dx (dx (fun t x => Real.log (Z t x))) t x
      = dx (dx Z) t x / Z t x - (dx Z t x / Z t x) ^ 2 := by
  have key : (fun y : ℝ => dx (fun t x => Real.log (Z t x)) t y)
      = fun y : ℝ => dx Z t y / Z t y := by
    funext y
    exact dx_log Z hreg hpos t y
  have hu : HasDerivAt (fun y : ℝ => dx Z t y) (dx (dx Z) t x) x := (hreg.space2 t x).hasDerivAt
  have hv : HasDerivAt (fun y : ℝ => Z t y) (dx Z t x) x := (hreg.space t x).hasDerivAt
  have hne : Z t x ≠ 0 := ne_of_gt (hpos t x)
  have hdiv : HasDerivAt (fun y : ℝ => dx Z t y / Z t y)
      ((dx (dx Z) t x * Z t x - dx Z t x * dx Z t x) / Z t x ^ 2) x := hu.div hv hne
  rw [dx_apply, key, hdiv.deriv]
  field_simp

/-- The space derivative of `exp h`. -/
