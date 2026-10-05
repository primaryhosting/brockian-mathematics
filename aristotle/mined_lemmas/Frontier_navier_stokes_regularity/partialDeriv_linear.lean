/-
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ContDiff

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-! ## Basic differential operators on `ℝ³` -/

/-- Physical space `ℝ³`. -/
abbrev Vec3 : Type := Fin 3 → ℝ

/-- The partial derivative `∂f/∂xᵢ` of a scalar field on `ℝ³`. -/

theorem partialDeriv_linear (c : Vec3) (j : Fin 3) (x : Vec3) :
    partialDeriv j (fun y : Vec3 => -∑ k, c k * y k) x = -c j := by
  have h : (fun y : Vec3 => -∑ k, c k * y k) = fun y : Vec3 =>
      (-(∑ k, (c k) • (ContinuousLinearMap.proj k : Vec3 →L[ℝ] ℝ)) : Vec3 →L[ℝ] ℝ) y := by
    funext y; simp
  rw [partialDeriv, h, ContinuousLinearMap.fderiv]
  simp [Pi.single_apply, Finset.sum_ite_eq']

/-- Spatially uniform flows are exact solutions of the Navier–Stokes system: for any (not
necessarily smooth) curve `f : ℝ → ℝ³`, the velocity `u (t, x) = f t` together with the linear
pressure `p (t, x) = -f'(t) · x` solves the equations.  This witnesses that the formalized
system admits nontrivial solutions; these solutions have infinite energy, so they are not
covered by `IsGlobalSmoothSolution`. -/
