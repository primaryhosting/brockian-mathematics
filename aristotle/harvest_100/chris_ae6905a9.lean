import Mathlib

/-!
# Conjugation To Momentum
Category: Gate1 Operator
Target: Brockian.DilationGenerator.conjugation_to_momentum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.DilationGenerator

open Real Complex

/-- Key intermediate lemma: for `f : ℝ → ℂ` differentiable at `Real.exp t`, the
transported function `s ↦ e^{s/2} • f (e^s)` has derivative
`e^{t/2} • ((1/2) * f (e^t) + e^t * deriv f (e^t))` at `t`. -/
theorem hasDerivAt_logSubstitution (f : ℝ → ℂ) (t : ℝ)
    (hf : DifferentiableAt ℝ f (Real.exp t)) :
    HasDerivAt (fun s : ℝ => Real.exp (s / 2) • f (Real.exp s))
      (Real.exp (t / 2) •
        ((1 / 2) * f (Real.exp t) + (Real.exp t : ℂ) * deriv f (Real.exp t))) t := by
  -- derivative of `s ↦ e^{s/2}` (as a complex-valued function)
  have hhalf : HasDerivAt (fun s : ℝ => s / 2) (1 / 2 : ℝ) t := by
    simpa using (hasDerivAt_id t).div_const 2
  have hexp2 : HasDerivAt (fun s : ℝ => Real.exp (s / 2))
      (Real.exp (t / 2) * (1 / 2)) t := hhalf.exp
  have hexp2C : HasDerivAt (fun s : ℝ => ((Real.exp (s / 2) : ℝ) : ℂ))
      (((Real.exp (t / 2) * (1 / 2) : ℝ) : ℂ)) t := hexp2.ofReal_comp
  -- derivative of `s ↦ f (e^s)`
  have hcomp : HasDerivAt (fun s : ℝ => f (Real.exp s))
      (Real.exp t • deriv f (Real.exp t)) t :=
    HasDerivAt.scomp t hf.hasDerivAt (Real.hasDerivAt_exp t)
  have hmul := hexp2C.mul hcomp
  have hsmul : HasDerivAt (fun s : ℝ => Real.exp (s / 2) • f (Real.exp s))
      (((Real.exp (t / 2) * (1 / 2) : ℝ) : ℂ) * f (Real.exp t) +
        ((Real.exp (t / 2) : ℝ) : ℂ) * (Real.exp t • deriv f (Real.exp t))) t := by
    simpa [Complex.real_smul] using hmul
  convert hsmul using 1
  push_cast [Complex.real_smul]
  ring

/-- **Conjugation to momentum (pointwise form).**
Under the log substitution `(U f)(t) = e^{t/2} f (e^t)`, the dilation generator
`A f = i ((1/2) f + x f')` transports to the momentum operator `i d/dt`:
`U (A f) (t) = i · (U f)' (t)`.

The hypothesis `hsupp` (compact support inside `(0, ∞)`) is part of the requested
statement; the pointwise identity in fact only uses smoothness of `f`. -/
theorem conjugation_to_momentum (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hsupp : HasCompactSupport f) (hsupp' : tsupport f ⊆ Set.Ioi (0 : ℝ)) (t : ℝ) :
    Real.exp (t / 2) •
        (Complex.I * ((1 / 2) * f (Real.exp t) + (Real.exp t : ℂ) * deriv f (Real.exp t))) =
      Complex.I * deriv (fun s : ℝ => Real.exp (s / 2) • f (Real.exp s)) t := by
  have hdiff : DifferentiableAt ℝ f (Real.exp t) := (hf.differentiable (by simp)) _
  rw [(hasDerivAt_logSubstitution f t hdiff).deriv]
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

