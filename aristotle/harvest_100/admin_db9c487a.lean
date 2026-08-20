/-
# Conjugation To Momentum
Category: Gate1 Operator
Target: Brockian.DilationGenerator.conjugation_to_momentum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian
namespace DilationGenerator

/-- The unitary implementing the logarithmic substitution on the core:
`(U f) t = e^{t/2} f (e^t)`. -/
noncomputable def logSubst (f : ℝ → ℂ) : ℝ → ℂ :=
  fun t => Real.exp (t / 2) • f (Real.exp t)

/-- Derivative of the log-substituted function, for `f` differentiable at `exp t`. -/
theorem hasDerivAt_logSubst {f : ℝ → ℂ} {t : ℝ}
    (hf : DifferentiableAt ℝ f (Real.exp t)) :
    HasDerivAt (logSubst f)
      (Real.exp (t / 2) •
        ((1 / 2) * f (Real.exp t) + (Real.exp t : ℂ) * deriv f (Real.exp t))) t := by
  have hexp2 : HasDerivAt (fun s : ℝ => Real.exp (s / 2)) (Real.exp (t / 2) * (1 / 2)) t := by
    have h : HasDerivAt (fun s : ℝ => s / 2) (1 / 2) t := by
      simpa using (hasDerivAt_id t).div_const 2
    simpa using (Real.hasDerivAt_exp (t / 2)).comp t h
  have hu : HasDerivAt (fun s : ℝ => ((Real.exp (s / 2) : ℝ) : ℂ))
      ((Real.exp (t / 2) * (1 / 2) : ℝ) : ℂ) t := hexp2.ofReal_comp
  have hv : HasDerivAt (fun s : ℝ => f (Real.exp s))
      (Real.exp t • deriv f (Real.exp t)) t :=
    (hf.hasDerivAt).scomp t (Real.hasDerivAt_exp t)
  have := hu.mul hv
  have hfun : (fun s : ℝ => ((Real.exp (s / 2) : ℝ) : ℂ) * f (Real.exp s)) = logSubst f := by
    funext s
    simp [logSubst, Complex.real_smul]
  simp only [Pi.mul_def] at this
  rw [hfun] at this
  convert this using 1
  simp [Complex.real_smul, Complex.ofReal_mul]
  ring

/-- **Conjugation to momentum.** Under the log substitution `(U f) t = e^{t/2} f (e^t)`,
the dilation generator `A f = i ((1/2) f + x f')` transports to the momentum operator
`i d/dt`: pointwise, `U (A f) t = i (U f)' t`.

The hypotheses of smoothness and compact support inside `(0, ∞)` are those of the
intended core; the proof only uses differentiability of `f` at `exp t`. -/
theorem conjugation_to_momentum {f : ℝ → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hsupp : tsupport f ⊆ Set.Ioi (0 : ℝ)) (t : ℝ) :
    Real.exp (t / 2) •
        (Complex.I * ((1 / 2) * f (Real.exp t) + (Real.exp t : ℂ) * deriv f (Real.exp t)))
      = Complex.I * deriv (fun s : ℝ => Real.exp (s / 2) • f (Real.exp s)) t := by
  have hdiff : DifferentiableAt ℝ f (Real.exp t) :=
    (hf.differentiable (by simp)).differentiableAt
  have h := (hasDerivAt_logSubst (f := f) (t := t) hdiff).deriv
  have hfun : (fun s : ℝ => Real.exp (s / 2) • f (Real.exp s)) = logSubst f := rfl
  rw [hfun, h]
  simp [Complex.real_smul]
  ring

end DilationGenerator
end Brockian

