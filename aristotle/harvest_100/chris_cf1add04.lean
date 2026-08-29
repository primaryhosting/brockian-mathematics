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
noncomputable def X (f : ℝ → ℂ) : ℝ → ℂ := fun x => (x : ℂ) * f x

/-- The momentum operator `P = -i ℏ d/dx` acting on complex-valued functions of a
real variable. -/
noncomputable def P (hbar : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x => -Complex.I * hbar * deriv f x

/-- Derivative of `y ↦ y * f y` for a Schwartz function `f`. -/
lemma hasDerivAt_mul_schwartz (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (y : ℂ) * f y) (f x + (x : ℂ) * deriv (⇑f) x) x := by
  have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x))
  have h2 : HasDerivAt (⇑f) (deriv (⇑f) x) x :=
    (f.differentiable x).hasDerivAt
  simpa [one_mul] using h1.mul h2

/-- **Canonical commutation relation.** On Schwartz space, with the position
operator `X` and the momentum operator `P = -i ℏ d/dx`, one has
`[X, P] = i ℏ`, i.e. `(X (P f) - P (X f)) x = i ℏ f x`. -/
theorem canonical_commutator (hbar : ℝ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    (X (P hbar ⇑f) - P hbar (X ⇑f)) x = Complex.I * hbar * f x := by
  have hX : X (⇑f) = fun y : ℝ => (y : ℂ) * f y := rfl
  have hd : deriv (X (⇑f)) x = f x + (x : ℂ) * deriv (⇑f) x := by
    rw [hX]
    exact (hasDerivAt_mul_schwartz f x).deriv
  simp only [Pi.sub_apply, X, P, hd]
  ring

/-!
### Operator form on Schwartz space

The same relation, stated as an identity of continuous linear operators on the
Schwartz space `𝓢(ℝ, ℂ)`, using Mathlib's multiplication and derivative operators.
-/

/-- The position operator as a continuous linear endomorphism of `𝓢(ℝ, ℂ)`:
`f ↦ (x ↦ f x * x)`. -/
noncomputable def posCLM : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ)
    Function.Complex.hasTemperateGrowth_ofReal

/-- The momentum operator `-i ℏ d/dx` as a continuous linear endomorphism of
`𝓢(ℝ, ℂ)`. -/
noncomputable def momCLM (hbar : ℝ) : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  (-Complex.I * hbar) • SchwartzMap.derivCLM ℂ ℂ

/-- Derivative of `y ↦ f y * y` for a Schwartz function `f`. -/
lemma hasDerivAt_schwartz_mul (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => f y * (y : ℂ)) (deriv (⇑f) x * x + f x) x := by
  have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x))
  have h2 : HasDerivAt (⇑f) (deriv (⇑f) x) x := (f.differentiable x).hasDerivAt
  simpa [mul_one] using h2.mul h1

/-- **Canonical commutation relation, operator form.** As continuous linear
operators on Schwartz space, `[posCLM, momCLM ℏ] = i ℏ • id`. -/
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

