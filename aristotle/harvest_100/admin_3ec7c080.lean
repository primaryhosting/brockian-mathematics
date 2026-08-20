/-
# Conjugation To Momentum
Category: Gate1 Operator
Target: Brockian.DilationGenerator.conjugation_to_momentum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.DilationGenerator

/-- Key intermediate lemma: the derivative of the log-substituted function
`s ↦ e^{s/2} • f (e^s)` at `t`, computed by the chain and product rules. -/
theorem hasDerivAt_log_substitution (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (s / 2) • f (Real.exp s))
      (Real.exp (t / 2) • ((1 / 2) * f (Real.exp t) + Real.exp t * deriv f (Real.exp t))) t := by
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (s / 2)) (Real.exp (t / 2) * (1 / 2)) t := by
    simpa using (Real.hasDerivAt_exp (t / 2)).comp t ((hasDerivAt_id t).div_const 2)
  have hexpC : HasDerivAt (fun s : ℝ => ((Real.exp (s / 2) : ℝ) : ℂ))
      ((Real.exp (t / 2) * (1 / 2) : ℝ) : ℂ) t := hexp.ofReal_comp
  have hfd : HasDerivAt f (deriv f (Real.exp t)) (Real.exp t) :=
    ((hf.differentiable (by simp)).differentiableAt).hasDerivAt
  have hcomp : HasDerivAt (fun s : ℝ => f (Real.exp s))
      (Real.exp t • deriv f (Real.exp t)) t :=
    hfd.scomp t (Real.hasDerivAt_exp t)
  have h : HasDerivAt (fun s : ℝ => ((Real.exp (s / 2) : ℝ) : ℂ) * f (Real.exp s))
      (((Real.exp (t / 2) * (1 / 2) : ℝ) : ℂ) * f (Real.exp t)
        + ((Real.exp (t / 2) : ℝ) : ℂ) * (Real.exp t • deriv f (Real.exp t))) t :=
    hexpC.mul hcomp
  have heq : (fun s : ℝ => ((Real.exp (s / 2) : ℝ) : ℂ) * f (Real.exp s))
      = fun s : ℝ => Real.exp (s / 2) • f (Real.exp s) := by
    funext s; simp [Complex.real_smul]
  rw [heq] at h
  convert h using 1
  push_cast [Complex.real_smul]
  ring

/-- Under the log substitution `U f (t) = e^{t/2} • f (e^t)`, the dilation generator
`A f (x) = i ((1/2) f x + x f' x)` transports to the momentum operator `i · d/dt`:
pointwise, `U (A f) (t) = i · (U f)' (t)`.

The hypothesis that `f` has compact support inside `(0, ∞)` is recorded (as requested)
but is not needed for this pointwise identity, which only uses smoothness of `f`. -/
theorem conjugation_to_momentum (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hsupp : HasCompactSupport f) (hsupp' : tsupport f ⊆ Set.Ioi (0 : ℝ)) (t : ℝ) :
    Real.exp (t / 2) •
        (Complex.I * ((1 / 2) * f (Real.exp t) + Real.exp t * deriv f (Real.exp t)))
      = Complex.I * deriv (fun s : ℝ => Real.exp (s / 2) • f (Real.exp s)) t := by
  rw [(hasDerivAt_log_substitution f hf t).deriv]
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

