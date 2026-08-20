import Mathlib

/-!
# Conjugation To Momentum
Category: Gate1 Operator
Target: Brockian.DilationGenerator.conjugation_to_momentum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.DilationGenerator

/-- The logarithmic substitution `(U f)(t) = e^{t/2} f(e^t)`. -/
noncomputable def logSubst (f : ℝ → ℂ) : ℝ → ℂ :=
  fun t => Real.exp (t / 2) • f (Real.exp t)

/-- Core computation: if `f` is differentiable at `e^t`, then `U f` is differentiable at `t`
with derivative `e^{t/2} ((1/2) f (e^t) + e^t f' (e^t))`. -/
theorem hasDerivAt_logSubst (f : ℝ → ℂ) (t : ℝ) (hf : DifferentiableAt ℝ f (Real.exp t)) :
    HasDerivAt (logSubst f)
      (Real.exp (t / 2) • ((1 / 2) * f (Real.exp t)
        + Real.exp t * deriv f (Real.exp t))) t := by
  have h1 : HasDerivAt (fun s : ℝ => ((Real.exp (s / 2) : ℝ) : ℂ))
      ((((1 : ℝ) / 2 * Real.exp (t / 2) : ℝ)) : ℂ) t := by
    have := ((Real.hasDerivAt_exp (t / 2)).comp t ((hasDerivAt_id t).div_const 2))
    simpa [mul_comm] using this.ofReal_comp
  have h2 : HasDerivAt (fun s : ℝ => f (Real.exp s))
      (Real.exp t • deriv f (Real.exp t)) t :=
    hf.hasDerivAt.scomp t (Real.hasDerivAt_exp t)
  have h3 := h1.mul h2
  have h4 : HasDerivAt (logSubst f)
      ((((1 : ℝ) / 2 * Real.exp (t / 2) : ℝ)) * f (Real.exp t)
        + ((Real.exp (t / 2) : ℝ) : ℂ) * (Real.exp t • deriv f (Real.exp t))) t := by
    simpa only [logSubst, Pi.mul_def, Complex.real_smul] using h3
  refine h4.congr_deriv ?_
  simp [Complex.real_smul]
  ring

/-- **Conjugation to momentum** (pointwise intertwining identity).

For `f : ℝ → ℂ` smooth with compact support contained in `(0, ∞)`, the dilation generator
`A f = i ((1/2) f + x f')` is transported by the logarithmic substitution
`(U f)(t) = e^{t/2} f(e^t)` to the momentum operator `i · d/dt`:
`U (A f) (t) = i · (U f)' (t)` for every `t : ℝ`.

Remark: the proof needs only differentiability of `f` at `e^t`; the smoothness and
compact-support hypotheses are stated because they describe the intended core, but are
not used (see `hasDerivAt_logSubst` for the general statement).

This is a pointwise identity only; no operator-level (essential self-adjointness) claim
is made here. -/
theorem conjugation_to_momentum (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hsupp : HasCompactSupport f) (hpos : tsupport f ⊆ Set.Ioi (0 : ℝ)) (t : ℝ) :
    Real.exp (t / 2) • (Complex.I * ((1 / 2) * f (Real.exp t)
        + Real.exp t * deriv f (Real.exp t)))
      = Complex.I * deriv (fun s => Real.exp (s / 2) • f (Real.exp s)) t := by
  have hd : DifferentiableAt ℝ f (Real.exp t) :=
    (hf.differentiable (by norm_num)) (Real.exp t)
  have h := (hasDerivAt_logSubst f t hd).deriv
  show Real.exp (t / 2) • (Complex.I * _) = Complex.I * deriv (logSubst f) t
  rw [h]
  simp [Complex.real_smul]
  ring

end Brockian.DilationGenerator

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

