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

/-- The unitary implementing the logarithmic substitution on the multiplicative half-line:
`(U f)(t) = e^{t/2} f(e^t)`. -/
noncomputable def logSubst (f : ℝ → ℂ) : ℝ → ℂ :=
  fun t => Real.exp (t / 2) • f (Real.exp t)

/-- Derivative of the log-substituted function `t ↦ e^{t/2} f(e^t)`, for differentiable `f`. -/
theorem hasDerivAt_logSubst (f : ℝ → ℂ) (hf : ∀ x : ℝ, DifferentiableAt ℝ f x) (t : ℝ) :
    HasDerivAt (logSubst f)
      (Real.exp (t / 2) •
        ((1 / 2) * f (Real.exp t) + Real.exp t * deriv f (Real.exp t))) t := by
  -- inner composition: `s ↦ f (e^s)`
  have hcomp : HasDerivAt (fun s : ℝ => f (Real.exp s))
      (Real.exp t • deriv f (Real.exp t)) t := by
    simpa [Function.comp] using ((hf (Real.exp t)).hasDerivAt).scomp t (Real.hasDerivAt_exp t)
  -- outer factor: `s ↦ (e^{s/2} : ℂ)`
  have hhalf : HasDerivAt (fun s : ℝ => s / 2) (1 / 2) t := by
    simpa using (hasDerivAt_id t).div_const 2
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (s / 2)) (Real.exp (t / 2) * (1 / 2)) t :=
    hhalf.exp
  have hexpC : HasDerivAt (fun s : ℝ => ((Real.exp (s / 2) : ℝ) : ℂ))
      ((Real.exp (t / 2) * (1 / 2) : ℝ) : ℂ) t := hexp.ofReal_comp
  have hmul := hexpC.mul hcomp
  have : logSubst f = fun s : ℝ => ((Real.exp (s / 2) : ℝ) : ℂ) * f (Real.exp s) := by
    funext s; simp [logSubst, Complex.real_smul]
  rw [this]
  convert hmul using 1
  push_cast [Complex.real_smul]
  ring

/-- **Conjugation to momentum.**  Under the logarithmic substitution `(U f)(t) = e^{t/2} f(e^t)`,
the dilation generator `A f = i ((1/2) f + x f')` transports to the momentum operator
`i d/dt`: pointwise, `U (A f) (t) = i (U f)' (t)`.

The hypotheses of compact support (`hsupp`, `hpos`) are those of the intended core of smooth,
compactly supported functions on `(0, ∞)`; they are recorded as requested even though the
pointwise identity only needs differentiability of `f`. -/
theorem conjugation_to_momentum (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (_hsupp : HasCompactSupport f) (_hpos : tsupport f ⊆ Set.Ioi (0 : ℝ)) (t : ℝ) :
    Real.exp (t / 2) •
        (Complex.I * ((1 / 2) * f (Real.exp t) + Real.exp t * deriv f (Real.exp t))) =
      Complex.I * deriv (fun s : ℝ => Real.exp (s / 2) • f (Real.exp s)) t := by
  have hdiff : ∀ x : ℝ, DifferentiableAt ℝ f x := fun x =>
    (hf.differentiable (by simp)).differentiableAt
  have h := (hasDerivAt_logSubst f hdiff t).deriv
  show _ = Complex.I * deriv (logSubst f) t
  rw [h, Complex.real_smul, Complex.real_smul]
  ring

end DilationGenerator
end Brockian

