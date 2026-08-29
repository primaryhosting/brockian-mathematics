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

theorem laplacian_const_mul {f : Vec3 → ℝ} (hf : ContDiff ℝ ∞ f) (c : ℝ) (x : Vec3) :
    laplacian (fun y => c * f y) x = c * laplacian f x := by
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  have h1 : ∀ i : Fin 3, partialDeriv i (fun y => c * f y) = fun y => c * partialDeriv i f y :=
    fun i => funext fun y => partialDeriv_const_mul hd c i y
  unfold laplacian
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h1 i, partialDeriv_const_mul ((contDiff_partialDeriv hf i).differentiable (by simp)) c i x]

