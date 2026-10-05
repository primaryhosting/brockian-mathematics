/-
# Canonical Commutator
Category: Quantum Physics
Target: QPhys.canonical_commutator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open SchwartzMap Complex

namespace QPhys

/-- The position operator `X : f ↦ (x ↦ x • f x)` acting on the Schwartz space
`𝓢(ℝ, ℂ)` of complex-valued Schwartz functions on the line. -/
noncomputable def position : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ))

/-- The momentum operator `P = -i ℏ d/dx` acting on the Schwartz space `𝓢(ℝ, ℂ)`. -/
noncomputable def momentum (hbar : ℝ) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  (-Complex.I * (hbar : ℂ)) • SchwartzMap.derivCLM ℂ ℂ

lemma hasTemperateGrowth_ofReal : (fun x : ℝ => (x : ℂ)).HasTemperateGrowth := by
  fun_prop

@[simp] lemma position_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) : position f x = (x : ℂ) * f x := by
  simp [position, smulLeftCLM_apply_apply hasTemperateGrowth_ofReal, smul_eq_mul]

@[simp] lemma momentum_apply (hbar : ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    momentum hbar f x = -Complex.I * hbar * deriv f x := by
  simp [momentum, smul_eq_mul]

/-- The derivative of `x ↦ x * f x` for a Schwartz function `f`, by the Leibniz rule. -/
lemma deriv_ofReal_mul (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    deriv (fun y : ℝ => (y : ℂ) * f y) x = f x + (x : ℂ) * deriv f x := by
  have h₁ : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
  have h₂ : HasDerivAt (fun y : ℝ => f y) (deriv f x) x := f.differentiableAt.hasDerivAt
  have h : HasDerivAt (fun y : ℝ => (y : ℂ) * f y) (1 * f x + (x : ℂ) * deriv f x) x :=
    h₁.mul h₂
  rw [h.deriv]
  ring

/-- **The canonical commutation relation.** On the Schwartz space `𝓢(ℝ, ℂ)`, the position
operator `X : f ↦ x f` and the momentum operator `P = -i ℏ d/dx` satisfy
`[X, P] = X P - P X = i ℏ`. -/
theorem canonical_commutator (hbar : ℝ) :
    position ∘L momentum hbar - momentum hbar ∘L position
      = (Complex.I * hbar) • ContinuousLinearMap.id ℂ 𝓢(ℝ, ℂ) := by
  ext f x
  have hpos : (fun y : ℝ => position f y) = fun y : ℝ => (y : ℂ) * f y := by
    funext y; exact position_apply f y
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    SchwartzMap.sub_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_id',
    id_eq, SchwartzMap.smul_apply, smul_eq_mul, momentum_apply, position_apply, hpos,
    deriv_ofReal_mul]
  ring

/-- Pointwise form of the canonical commutation relation:
`x · (-iℏ f'(x)) - (-iℏ (d/dx)(x f)(x)) = iℏ f x`. -/
theorem canonical_commutator_apply (hbar : ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    position (momentum hbar f) x - momentum hbar (position f) x
      = Complex.I * hbar * f x := by
  have := congrArg (fun L : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) => L f x) (canonical_commutator hbar)
  simpa using this

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

