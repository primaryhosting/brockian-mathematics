import Mathlib

/-!
# Canonical Commutator
Category: Quantum Physics
Target: QPhys.canonical_commutator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace QPhys

open SchwartzMap

/-- The multiplication-by-`x` function `ℝ → ℂ` has temperate growth. -/
theorem hasTemperateGrowth_ofReal :
    Function.HasTemperateGrowth (fun x : ℝ => (x : ℂ)) := by
  fun_prop

/-- The position operator `X : ψ ↦ (x ↦ x · ψ x)` on Schwartz space `𝓢(ℝ, ℂ)`. -/
noncomputable def posOp : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ))

/-- The momentum operator `P = -i ℏ d/dx` on Schwartz space `𝓢(ℝ, ℂ)`. -/
noncomputable def momOp (hbar : ℝ) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  (-(Complex.I * (hbar : ℂ))) • SchwartzMap.derivCLM ℂ ℂ

@[simp]
theorem posOp_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) : posOp f x = (x : ℂ) * f x := by
  simp [posOp, SchwartzMap.smulLeftCLM_apply_apply hasTemperateGrowth_ofReal,
    smul_eq_mul]

@[simp]
theorem momOp_apply (hbar : ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    momOp hbar f x = -(Complex.I * (hbar : ℂ)) * deriv f x := by
  simp [momOp, smul_eq_mul]

/-- The derivative of `x ↦ x · f x` for a Schwartz function `f`. -/
theorem deriv_ofReal_mul (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    deriv (fun x : ℝ => (x : ℂ) * f x) x = f x + (x : ℂ) * deriv f x := by
  have h₁ : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 x := by
    simpa using Complex.ofRealCLM.hasDerivAt (x := x)
  have h₂ : HasDerivAt (fun x : ℝ => f x) (deriv f x) x := f.hasDerivAt x
  have := h₁.mul h₂
  simpa [one_mul, mul_comm] using this.deriv

/-- **Canonical commutation relation.**  On Schwartz space `𝓢(ℝ, ℂ)`, with the position
operator `X : ψ ↦ x ψ` and the momentum operator `P = -i ℏ d/dx`, one has
`[X, P] = X P - P X = i ℏ`. -/
theorem canonical_commutator (hbar : ℝ) :
    posOp ∘L momOp hbar - momOp hbar ∘L posOp
      = (Complex.I * (hbar : ℂ)) • ContinuousLinearMap.id ℂ 𝓢(ℝ, ℂ) := by
  ext f x
  have hXP : (posOp (momOp hbar f)) x
      = (x : ℂ) * (-(Complex.I * (hbar : ℂ)) * deriv f x) := by
    simp
  have hPX : (momOp hbar (posOp f)) x
      = -(Complex.I * (hbar : ℂ)) * (f x + (x : ℂ) * deriv f x) := by
    have hfun : ⇑(posOp f) = fun x : ℝ => (x : ℂ) * f x := by
      funext y; simp
    rw [momOp_apply, hfun, deriv_ofReal_mul f x]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    SchwartzMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, SchwartzMap.smul_apply, smul_eq_mul,
    hXP, hPX]
  ring

/-- Pointwise form of the canonical commutation relation:
`(X P ψ)(x) - (P X ψ)(x) = i ℏ ψ(x)`. -/
theorem canonical_commutator_apply (hbar : ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    posOp (momOp hbar f) x - momOp hbar (posOp f) x
      = (Complex.I * (hbar : ℂ)) * f x := by
  have := congrArg (fun T : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) => T f x) (canonical_commutator hbar)
  simpa [smul_eq_mul] using this

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

