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

theorem isKPZSolution_log (xi Z : ℝ → ℝ → ℝ) (hreg : SpaceTimeReg Z)
    (hpos : ∀ t x : ℝ, 0 < Z t x) (hZ : IsSHESolution xi Z) :
    IsKPZSolution xi (fun t x => Real.log (Z t x)) := by
  intro t x
  have hne : Z t x ≠ 0 := ne_of_gt (hpos t x)
  rw [dt_log Z hreg hpos, dx_dx_log Z hreg hpos, dx_log Z hreg hpos, hZ t x]
  field_simp
  ring

/-- **Cole–Hopf, backward direction.** If `h` solves the KPZ equation with noise `ξ`, then
`Z = exp h` is a positive solution of the multiplicative stochastic heat equation with the
same noise. -/
