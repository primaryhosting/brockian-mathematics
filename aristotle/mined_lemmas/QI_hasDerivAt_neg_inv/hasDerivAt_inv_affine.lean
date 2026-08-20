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

import Mathlib

/-!
# Scalar integrals used in the integral representations
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace QI


theorem hasDerivAt_inv_affine (M D : Mat n) {s : ℝ} (h : IsUnit (M + (s : ℂ) • D)) :
    HasDerivAt (fun u : ℝ => (M + (u : ℂ) • D)⁻¹)
      (-((M + (s : ℂ) • D)⁻¹ * D * (M + (s : ℂ) • D)⁻¹)) s := by
  obtain ⟨u, hu⟩ := h
  have hfd : HasFDerivAt Ring.inverse
      (-(ContinuousLinearMap.mulLeftRight ℂ (Mat n) (↑u⁻¹ : Mat n) (↑u⁻¹ : Mat n)))
      (M + (s : ℂ) • D) := by
    rw [← hu]
    exact hasFDerivAt_ringInverse u
  have haff : HasDerivAt (fun v : ℝ => M + (v : ℂ) • D) D s := by
    have h1 : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 s := Complex.ofRealCLM.hasDerivAt
    simpa using ((h1.smul_const D).const_add M)
  have hcomp := (hfd.restrictScalars ℝ).comp_hasDerivAt s haff
  have hinv : ∀ X : Mat n, Ring.inverse X = X⁻¹ := fun X =>
    (Matrix.nonsing_inv_eq_ringInverse X).symm
  simp only [Function.comp_def, hinv] at hcomp
  convert hcomp using 1
  have huinv : (↑u⁻¹ : Mat n) = (M + (s : ℂ) • D)⁻¹ := by
    rw [← hu, Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_unit]
  simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, huinv]

/-- The derivative of the resolvent along the path. -/
