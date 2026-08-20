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

theorem dx_dx_exp (h : ℝ → ℝ → ℝ) (hreg : SpaceTimeReg h) (t x : ℝ) :
    dx (dx (fun t x => Real.exp (h t x))) t x
      = Real.exp (h t x) * (dx (dx h) t x + (dx h t x) ^ 2) := by
  have key : (fun y : ℝ => dx (fun t x => Real.exp (h t x)) t y)
      = fun y : ℝ => Real.exp (h t y) * dx h t y := by
    funext y
    exact dx_exp h hreg t y
  have hu : HasDerivAt (fun y : ℝ => Real.exp (h t y)) (Real.exp (h t x) * dx h t x) x :=
    ((hreg.space t x).hasDerivAt).exp
  have hv : HasDerivAt (fun y : ℝ => dx h t y) (dx (dx h) t x) x := (hreg.space2 t x).hasDerivAt
  have hmul : HasDerivAt (fun y : ℝ => Real.exp (h t y) * dx h t y)
      (Real.exp (h t x) * dx h t x * dx h t x + Real.exp (h t x) * dx (dx h) t x) x := hu.mul hv
  rw [dx_apply, key, hmul.deriv]
  ring

/-! ## Regularity is preserved by the Cole–Hopf transform -/

