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

/-! ## Differential operators on `ℝ³` -/

/-- Three dimensional Euclidean space. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The `i`-th partial derivative of a (vector or scalar valued) field on `ℝ³`. -/

lemma convective_scale (u : E3 → E3) (hu : Differentiable ℝ u) (c : ℝ) (x : E3) :
    convective (fun y => c • u (c • y)) x = c ^ 3 • convective u (c • x) := by
  have h1 : HasFDerivAt (fun y : E3 => c • u (c • y))
      (c • ((fderiv ℝ u (c • x)).comp (c • ContinuousLinearMap.id ℝ E3))) x :=
    ((((hu (c • x)).hasFDerivAt).comp x ((hasFDerivAt_id x).const_smul c)).const_smul c)
  simp only [convective, h1.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.coe_id', id_eq, map_smul, smul_smul]
  ring_nf

/-- Space regularity of a Navier–Stokes solution at a fixed time. -/
