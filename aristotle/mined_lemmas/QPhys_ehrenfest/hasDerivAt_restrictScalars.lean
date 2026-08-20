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

namespace QPhys

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Differentiability of a (possibly time-dependent) bounded operator, transported along
`restrictScalars ℝ`. -/

lemma hasDerivAt_restrictScalars {A : ℝ → (E →L[ℂ] E)} {A' : E →L[ℂ] E} {t : ℝ}
    (hA : HasDerivAt A A' t) :
    HasDerivAt (fun s => (A s).restrictScalars ℝ) (A'.restrictScalars ℝ) t := by
  have hL : HasFDerivAt (fun B : E →L[ℂ] E => B.restrictScalars ℝ)
      (ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ) (A t) :=
    (ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ).hasFDerivAt
  simpa using hL.comp_hasDerivAt t hA

/-- The time derivative of `s ↦ (A s) (ψ s)` for a differentiable operator-valued function `A`
and a differentiable vector-valued function `ψ`. -/
