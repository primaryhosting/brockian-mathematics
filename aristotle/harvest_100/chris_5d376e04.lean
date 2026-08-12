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

We realize the position operator `x` and the momentum operator `p = -i ℏ d/dx` as
continuous linear endomorphisms of the Schwartz space `𝓢(ℝ, ℂ)`, and prove the
canonical commutation relation `⁅x, p⁆ = i ℏ`.
-/

namespace QPhys

open SchwartzMap

/-- The position operator on Schwartz space: `(x · f) (t) = t * f t`. -/
noncomputable def posOp : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun t : ℝ => (t : ℂ))

/-- The momentum operator on Schwartz space: `p = -i ℏ d/dx`. -/
noncomputable def momOp (hbar : ℝ) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  (-(Complex.I * hbar)) • SchwartzMap.derivCLM ℂ ℂ

theorem ofReal_hasTemperateGrowth : Function.HasTemperateGrowth (fun t : ℝ => (t : ℂ)) :=
  Complex.ofRealCLM.hasTemperateGrowth

@[simp] theorem posOp_apply (f : 𝓢(ℝ, ℂ)) (t : ℝ) : QPhys.posOp f t = (t : ℂ) * f t := by
  simp [QPhys.posOp, QPhys.ofReal_hasTemperateGrowth, smul_eq_mul]

@[simp] theorem momOp_apply (hbar : ℝ) (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    QPhys.momOp hbar f t = -(Complex.I * hbar) * deriv f t := by
  simp [QPhys.momOp]

/-- Leibniz rule for the position operator: `(t * f t)' = f t + t * f' t`. -/
theorem deriv_ofReal_mul (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    deriv (fun s : ℝ => (s : ℂ) * f s) t = f t + (t : ℂ) * deriv f t := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
    simpa using Complex.ofRealCLM.hasDerivAt (x := t)
  simpa using (h1.mul (f.hasDerivAt t)).deriv

/-- **Canonical commutation relation.** On the Schwartz space `𝓢(ℝ, ℂ)`, the position
operator `x` (multiplication by the coordinate) and the momentum operator
`p = -i ℏ d/dx` satisfy `[x, p] = i ℏ`. -/
theorem canonical_commutator (hbar : ℝ) :
    ⁅QPhys.posOp, QPhys.momOp hbar⁆
      = (Complex.I * hbar) • ContinuousLinearMap.id ℂ 𝓢(ℝ, ℂ) := by
  ext f t
  have hposf : (QPhys.posOp f : ℝ → ℂ) = fun s : ℝ => (s : ℂ) * f s := by
    funext s; exact QPhys.posOp_apply f s
  simp [Ring.lie_def, hposf, QPhys.deriv_ofReal_mul f t]
  ring

end QPhys

#print axioms QPhys.canonical_commutator

