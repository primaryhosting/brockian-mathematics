/-
# Canonical Commutator
Category: Quantum Physics
Target: QPhys.canonical_commutator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

open Complex

/-- The position operator `X : f ↦ (x ↦ x · f x)` acting on complex-valued
functions of a real variable. -/

theorem canonical_commutator_CLM (hbar : ℝ) :
    posCLM.comp (momCLM hbar) - (momCLM hbar).comp posCLM
      = (Complex.I * hbar) • ContinuousLinearMap.id ℂ (SchwartzMap ℝ ℂ) := by
  refine ContinuousLinearMap.ext fun f => SchwartzMap.ext fun x => ?_
  have h2 : deriv (fun y : ℝ => f y * (y : ℂ)) x = deriv (⇑f) x * x + f x :=
    (hasDerivAt_schwartz_mul f x).deriv
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.id_apply,
    SchwartzMap.sub_apply, SchwartzMap.smul_apply, posCLM, momCLM,
    SchwartzMap.bilinLeftCLM_apply, SchwartzMap.derivCLM_apply,
    ContinuousLinearMap.mul_apply', smul_eq_mul, h2]
  ring

end QPhys

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

