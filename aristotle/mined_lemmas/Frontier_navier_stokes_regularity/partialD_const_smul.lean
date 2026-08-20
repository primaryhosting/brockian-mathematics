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

lemma partialD_const_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E3 → F) (c : ℝ) (i : Fin 3) (x : E3) (hf : DifferentiableAt ℝ f x) :
    partialD i (fun y => c • f y) x = c • partialD i f x := by
  have h : fderiv ℝ (fun y => c • f y) x = c • fderiv ℝ f x := fderiv_const_smul hf c
  simp [partialD, h]

