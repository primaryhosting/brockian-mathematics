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

/-!
# The canonical commutation relation on Schwartz space

We define the position operator `X : f ↦ (x ↦ x * f x)` and the momentum operator
`P ħ : f ↦ (x ↦ -i ħ f'(x))` as continuous linear endomorphisms of the Schwartz space
`𝓢(ℝ, ℂ)`, and prove the canonical commutation relation `[X, P ħ] = i ħ · id`.
-/

namespace QPhys

open SchwartzMap

/-- The coordinate function `x ↦ (x : ℂ)` has temperate growth. -/
theorem hasTemperateGrowth_coe : Function.HasTemperateGrowth (fun x : ℝ => (x : ℂ)) :=
  Function.Complex.hasTemperateGrowth_ofReal

/-- The position operator on Schwartz space: multiplication by the coordinate `x`. -/
noncomputable def position : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ))

/-- The momentum operator on Schwartz space, `p = -i ħ d/dx`. -/
noncomputable def momentum (ħ : ℝ) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  (-(Complex.I * ħ)) • SchwartzMap.derivCLM ℂ ℂ

@[simp]
theorem position_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) : position f x = (x : ℂ) * f x := by
  simp [position, SchwartzMap.smulLeftCLM_apply_apply hasTemperateGrowth_coe]

@[simp]
theorem momentum_apply (ħ : ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    momentum ħ f x = -(Complex.I * ħ) * deriv (⇑f) x := by
  simp [momentum, SchwartzMap.derivCLM_apply]

theorem deriv_coe (x : ℝ) : deriv (fun y : ℝ => (y : ℂ)) x = 1 := by
  have h : (fun y : ℝ => (y : ℂ)) = fun y : ℝ => Complex.ofRealCLM y := rfl
  rw [h, ContinuousLinearMap.deriv]
  simp

/-- Leibniz rule for the position operator. -/
theorem deriv_position (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    deriv (⇑(position f)) x = f x + x * deriv (⇑f) x := by
  have he : (⇑(position f)) = fun y : ℝ => (y : ℂ) * f y := funext (position_apply f)
  rw [he, deriv_fun_mul (c := fun y : ℝ => (y : ℂ)) Complex.ofRealCLM.differentiableAt
    f.differentiableAt, deriv_coe]
  ring

/-- The canonical commutation relation, pointwise form:
`(x p - p x) f (t) = i ħ · f t` for every Schwartz function `f`. -/
theorem canonical_commutator_apply (ħ : ℝ) (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    (position (momentum ħ f) - momentum ħ (position f)) t = Complex.I * ħ * f t := by
  simp only [SchwartzMap.sub_apply, position_apply, momentum_apply, deriv_position]
  ring

/-- **Canonical commutation relation** on Schwartz space:
with the position operator `x` (multiplication by the coordinate) and the momentum operator
`p = -i ħ d/dx`, one has `[x, p] = i ħ`. -/
theorem canonical_commutator (ħ : ℝ) :
    position ∘L momentum ħ - momentum ħ ∘L position
      = (Complex.I * ħ) • ContinuousLinearMap.id ℂ 𝓢(ℝ, ℂ) := by
  ext f t
  simpa using canonical_commutator_apply ħ f t

/-- The canonical commutation relation phrased with the ring commutator bracket:
`⁅x, p⁆ = i ħ · 1` in the algebra of continuous linear endomorphisms of `𝓢(ℝ, ℂ)`. -/
theorem lie_position_momentum (ħ : ℝ) :
    ⁅position, momentum ħ⁆ = (Complex.I * ħ) • (1 : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)) := by
  simpa [Ring.lie_def] using canonical_commutator ħ

end QPhys

