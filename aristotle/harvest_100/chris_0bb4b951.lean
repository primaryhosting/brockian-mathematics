/-
# Canonical Commutator
Category: Quantum Physics
Target: QPhys.canonical_commutator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any doc comment, so the required header appears above as a
-- plain block comment and is repeated verbatim as the module docstring after the import.)

import Mathlib

/-!
# Canonical Commutator
Category: Quantum Physics
Target: QPhys.canonical_commutator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open SchwartzMap

namespace QPhys

/-- The position operator `x` acting on the Schwartz space `𝓢(ℝ, ℂ)`,
i.e. multiplication by the coordinate function. -/
noncomputable def posOp : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) := smulLeftCLM ℂ (fun x : ℝ => (x : ℂ))

/-- The momentum operator `p = -i ℏ d/dx` acting on the Schwartz space `𝓢(ℝ, ℂ)`. -/
noncomputable def momOp (hbar : ℝ) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  (-(Complex.I * hbar)) • derivCLM ℂ ℂ

@[simp]
theorem posOp_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) : posOp f x = (x : ℂ) * f x := by
  simp [posOp, smulLeftCLM_apply_apply (g := fun x : ℝ => (x : ℂ)) (by fun_prop), smul_eq_mul]

@[simp]
theorem momOp_apply (hbar : ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    momOp hbar f x = -(Complex.I * hbar) * deriv f x := by
  simp [momOp, smul_eq_mul]

/-- **Canonical commutation relation.** On the Schwartz space `𝓢(ℝ, ℂ)`, with the position
operator `x` (multiplication by the coordinate) and the momentum operator `p = -i ℏ d/dx`,
one has `[x, p] = x p - p x = i ℏ`. -/
theorem canonical_commutator (hbar : ℝ) :
    posOp ∘L momOp hbar - momOp hbar ∘L posOp
      = (Complex.I * hbar) • ContinuousLinearMap.id ℂ 𝓢(ℝ, ℂ) := by
  have hg : Function.HasTemperateGrowth (fun x : ℝ => (x : ℂ)) := by fun_prop
  ext f x
  have hfun : ⇑((smulLeftCLM ℂ fun x : ℝ => (x : ℂ)) f) = fun y : ℝ => (y : ℂ) * f y := by
    funext y; simp [smulLeftCLM_apply_apply hg, smul_eq_mul]
  have hd : deriv (⇑((smulLeftCLM ℂ fun x : ℝ => (x : ℂ)) f)) x = f x + x * deriv f x := by
    rw [hfun]
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := x))
    have h : HasDerivAt (fun y : ℝ => (y : ℂ) * f y) (1 * f x + x * deriv f x) x :=
      h1.mul (f.hasDerivAt x)
    rw [h.deriv]; ring
  simp only [ContinuousLinearMap.coe_sub', Pi.sub_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, SchwartzMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_id', id_eq, SchwartzMap.smul_apply, smul_eq_mul, posOp, momOp,
    derivCLM_apply, smulLeftCLM_apply_apply hg]
  rw [hd]
  ring

/-- Pointwise form of the canonical commutation relation:
`(x p f - p x f)(t) = i ℏ f t` for every Schwartz function `f` and every `t : ℝ`. -/
theorem canonical_commutator_apply (hbar : ℝ) (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    posOp (momOp hbar f) t - momOp hbar (posOp f) t = Complex.I * hbar * f t := by
  have := congrArg (fun T : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) => (T f) t) (canonical_commutator hbar)
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

