/-
# Canonical Commutator
Category: Quantum Physics
Target: QPhys.canonical_commutator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` because Lean 4 does not allow a
-- module docstring to precede `import`; the exact docstring is repeated below.)

import Mathlib

/-!
# Canonical Commutator
Category: Quantum Physics
Target: QPhys.canonical_commutator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace QPhys

open SchwartzMap

/-- The function `x ↦ (x : ℂ)` has temperate growth (it is a continuous linear map). -/
theorem ofReal_hasTemperateGrowth : (fun x : ℝ => (x : ℂ)).HasTemperateGrowth :=
  Complex.ofRealCLM.hasTemperateGrowth

/-- The position operator `X : f ↦ (x ↦ x * f x)` on the Schwartz space `𝓢(ℝ, ℂ)`. -/
noncomputable def positionOp : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ))

/-- The momentum operator `P = -i ℏ d/dx` on the Schwartz space `𝓢(ℝ, ℂ)`. -/
noncomputable def momentumOp (ℏ : ℝ) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  (-(Complex.I * (ℏ : ℂ))) • SchwartzMap.derivCLM ℂ ℂ

@[simp]
theorem positionOp_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) : positionOp f x = (x : ℂ) * f x := by
  simp [positionOp, SchwartzMap.smulLeftCLM_apply_apply ofReal_hasTemperateGrowth,
    smul_eq_mul]

@[simp]
theorem momentumOp_apply (ℏ : ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    momentumOp ℏ f x = -(Complex.I * (ℏ : ℂ)) * deriv (⇑f) x := by
  simp [momentumOp, smul_eq_mul]

/-- The derivative of `x ↦ x * f x` for a Schwartz function `f`. -/
theorem hasDerivAt_mul_schwartz (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (y : ℂ) * f y) (f x + (x : ℂ) * deriv (⇑f) x) x := by
  have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
  have h2 := f.hasDerivAt x
  simpa using h1.mul h2

/-- **Canonical commutation relation.** On Schwartz space, with the position operator
`X : f ↦ (x ↦ x f x)` and the momentum operator `P = -i ℏ d/dx`, one has
`[X, P] = i ℏ • id`. -/
theorem canonical_commutator (ℏ : ℝ) :
    ⁅positionOp, momentumOp ℏ⁆
      = (Complex.I * (ℏ : ℂ)) • (ContinuousLinearMap.id ℂ 𝓢(ℝ, ℂ)) := by
  ext f x
  have hderiv : deriv (fun y : ℝ => (y : ℂ) * f y) x = f x + (x : ℂ) * deriv (⇑f) x :=
    (hasDerivAt_mul_schwartz f x).deriv
  have hXf : ⇑(positionOp f) = fun y : ℝ => (y : ℂ) * f y := by
    funext y; simp
  simp only [Ring.lie_def, ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
    SchwartzMap.sub_apply, momentumOp_apply, positionOp_apply, hXf, hderiv,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_id', id_eq,
    SchwartzMap.smul_apply, smul_eq_mul]
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

