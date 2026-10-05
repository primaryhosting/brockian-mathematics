import Mathlib

/-!
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

open Complex MeasureTheory intervalIntegral
open scoped InnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## Phases -/

/-- The unimodular phase `u ↦ exp (i r u)`. -/

theorem hasDerivAt_clmApply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (A DA : ℝ → E →L[ℂ] F) (v : ℝ → E) (v' : F) (dv : E) (s : ℝ)
    (hA : HasDerivAt A (DA s) s) (hv : HasDerivAt v dv s) (hv' : v' = DA s (v s) + A s dv) :
    HasDerivAt (fun t => A t (v t)) v' s := by
  subst hv'
  have hRS : HasDerivAt (fun t => (A t).restrictScalars ℝ) ((DA s).restrictScalars ℝ) s :=
    ((ContinuousLinearMap.restrictScalarsL ℂ E F ℝ ℝ).hasFDerivAt).comp_hasDerivAt s hA
  exact hRS.clm_apply hv

/-! ## The instantaneous Hamiltonian -/

/-- The instantaneous Hamiltonian with (real) eigenvalue `e₁` on the range of the projection
`P s` and eigenvalue `e₂` on its kernel. -/
