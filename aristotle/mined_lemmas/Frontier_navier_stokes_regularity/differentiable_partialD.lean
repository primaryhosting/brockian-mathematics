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

lemma differentiable_partialD {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E3 → F) (hf : ContDiff ℝ (2 : ℕ) f) (i : Fin 3) :
    Differentiable ℝ (fun y => partialD i f y) := by
  have h1 : ContDiff ℝ (1 : ℕ) (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have h2 : Differentiable ℝ (fderiv ℝ f) := h1.differentiable (by norm_num)
  exact ((ContinuousLinearMap.apply ℝ F (EuclideanSpace.single i (1 : ℝ))).differentiable).comp h2

