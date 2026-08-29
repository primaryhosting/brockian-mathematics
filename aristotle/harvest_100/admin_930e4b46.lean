import Mathlib

/-!
# Canonical Commutator
Category: Quantum Physics
Target: QPhys.canonical_commutator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

open SchwartzMap Complex

/-- The position operator `X : f ↦ (x ↦ x * f x)` as a continuous linear operator on the
Schwartz space `𝓢(ℝ, ℂ)`. -/
noncomputable def posOp : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  smulLeftCLM ℂ (fun x : ℝ => (x : ℂ))

/-- The momentum operator `p = -i ℏ d/dx` as a continuous linear operator on the
Schwartz space `𝓢(ℝ, ℂ)`. -/
noncomputable def momOp (hbar : ℝ) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  (-Complex.I * hbar) • derivCLM ℂ ℂ

@[simp] theorem posOp_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) : posOp f x = (x : ℂ) * f x := by
  simp [posOp, smulLeftCLM_apply_apply Function.Complex.hasTemperateGrowth_ofReal,
    smul_eq_mul]

@[simp] theorem momOp_apply (hbar : ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    momOp hbar f x = (-Complex.I * hbar) * deriv f x := by
  simp [momOp, derivCLM_apply, smul_eq_mul]

/-- Derivative of `x ↦ x * f x` for a Schwartz function `f`. -/
theorem hasDerivAt_mul_ofReal (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (y : ℂ) * f y) (f x + (x : ℂ) * deriv f x) x := by
  have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x))
  simpa [one_mul] using h1.mul (f.hasDerivAt x)

/-- **Canonical commutation relation** on Schwartz space: with the position operator
`x` and the momentum operator `p = -i ℏ d/dx`, one has `[x, p] = i ℏ`. -/
theorem canonical_commutator (hbar : ℝ) :
    posOp ∘L momOp hbar - momOp hbar ∘L posOp
      = ((Complex.I * hbar) • ContinuousLinearMap.id ℂ 𝓢(ℝ, ℂ)) := by
  ext f x
  have hd : deriv (fun y : ℝ => (y : ℂ) * f y) x = f x + (x : ℂ) * deriv f x :=
    (hasDerivAt_mul_ofReal f x).deriv
  have hpos : ⇑(posOp f) = fun y : ℝ => (y : ℂ) * f y := by
    funext y; simp
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_id',
    SchwartzMap.sub_apply, SchwartzMap.smul_apply, id_eq,
    posOp_apply, momOp_apply, hpos, hd, smul_eq_mul]
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

