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

theorem deriv_position (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    deriv (⇑(position f)) x = f x + x * deriv (⇑f) x := by
  have he : (⇑(position f)) = fun y : ℝ => (y : ℂ) * f y := funext (position_apply f)
  rw [he, deriv_fun_mul (c := fun y : ℝ => (y : ℂ)) Complex.ofRealCLM.differentiableAt
    f.differentiableAt, deriv_coe]
  ring

/-- The canonical commutation relation, pointwise form:
`(x p - p x) f (t) = i ħ · f t` for every Schwartz function `f`. -/
