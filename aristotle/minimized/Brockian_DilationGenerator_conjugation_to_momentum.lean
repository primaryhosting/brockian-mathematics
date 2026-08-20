import Mathlib

/-!
# Conjugation To Momentum
Category: Gate1 Operator
Target: Brockian.DilationGenerator.conjugation_to_momentum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Brockian.DilationGenerator

/-- The unitary implementing the logarithmic substitution on the core:
`(U f) t = e^{t/2} f (e^t)`. -/
noncomputable def logSubst (f : ℝ → ℂ) : ℝ → ℂ := fun t => Real.exp (t / 2) • f (Real.exp t)

/-- Derivative of the log-substituted function: for `f` differentiable at `e^t`,
`(U f)' t = e^{t/2} ((1/2) f (e^t) + e^t f' (e^t))`. -/
theorem hasDerivAt_logSubst (f : ℝ → ℂ) (t : ℝ) (hf : DifferentiableAt ℝ f (Real.exp t)) :
    HasDerivAt (logSubst f)
      (Real.exp (t / 2) • ((1 / 2) * f (Real.exp t) + Real.exp t * deriv f (Real.exp t))) t := by
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (s / 2)) (Real.exp (t / 2) * (1 / 2)) t := by
    simpa using (Real.hasDerivAt_exp (t / 2)).comp t
      ((hasDerivAt_id t).div_const 2)
  have hexp' : HasDerivAt (fun s : ℝ => ((Real.exp (s / 2) : ℝ) : ℂ))
      ((Real.exp (t / 2) * (1 / 2) : ℝ) : ℂ) t := hexp.ofReal_comp
  have hexp1 : HasDerivAt (fun s : ℝ => Real.exp s) (Real.exp t) t := Real.hasDerivAt_exp t
  have hcomp : HasDerivAt (fun s : ℝ => f (Real.exp s))
      (Real.exp t • deriv f (Real.exp t)) t :=
    (hf.hasDerivAt).scomp t hexp1
  have hmul := hexp'.mul hcomp
  have hfun : logSubst f = fun s : ℝ => ((Real.exp (s / 2) : ℝ) : ℂ) * f (Real.exp s) := by
    funext s
    simp [logSubst, Complex.real_smul]
  rw [hfun]
  convert hmul using 1
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat]
  ring

/-- **Conjugation of the dilation generator to the momentum operator.**

Under the log substitution `(U f) t = e^{t/2} f (e^t)`, the dilation generator
`A f = i ((1/2) f + x f')` transports to the momentum operator `i d/dt`:
`U (A f) = i (U f)'` pointwise.

The hypotheses `hsmooth` (smoothness) and `hsupp` (compact support inside `(0, ∞)`) are those
of the intended core; only differentiability of `f` at `e^t`, which follows from `hsmooth`,
is actually used. -/
theorem conjugation_to_momentum (f : ℝ → ℂ) (hsmooth : ContDiff ℝ (⊤ : ℕ∞) f)
    (hsupp : tsupport f ⊆ Set.Ioi (0 : ℝ)) (t : ℝ) :
    Real.exp (t / 2) •
        (Complex.I * ((1 / 2) * f (Real.exp t) + Real.exp t * deriv f (Real.exp t))) =
      Complex.I * deriv (fun s : ℝ => Real.exp (s / 2) • f (Real.exp s)) t := by
  have hf : DifferentiableAt ℝ f (Real.exp t) := (hsmooth.differentiable (by simp)).differentiableAt
  have hd := (hasDerivAt_logSubst f t hf).deriv
  rw [show (fun s : ℝ => Real.exp (s / 2) • f (Real.exp s)) = logSubst f from rfl, hd]
  simp [Complex.real_smul]
  ring

end Brockian.DilationGenerator

