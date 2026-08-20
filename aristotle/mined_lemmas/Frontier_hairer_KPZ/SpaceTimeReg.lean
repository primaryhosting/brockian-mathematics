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

theorem SpaceTimeReg.exp (h : ℝ → ℝ → ℝ) (hreg : SpaceTimeReg h) :
    SpaceTimeReg (fun t x => Real.exp (h t x)) where
  time t x := (hreg.time t x).exp
  space t x := (hreg.space t x).exp
  space2 t x := by
    have key : (fun y : ℝ => dx (fun t x => Real.exp (h t x)) t y)
        = fun y : ℝ => Real.exp (h t y) * dx h t y := by
      funext y
      exact dx_exp h hreg t y
    rw [key]
    exact ((hreg.space t x).exp).mul (hreg.space2 t x)

/-! ## The Cole–Hopf reduction -/

/-- **Cole–Hopf, forward direction.** If `Z > 0` solves the multiplicative stochastic heat
equation with noise `ξ`, then `h = log Z` solves the KPZ equation with the same noise. -/
