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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian
namespace DilationGenerator

/-- The unitary `U` implementing the logarithmic substitution on the core:
`(U f) t = e^{t/2} f(e^t)`. -/
noncomputable def logSubst (f : ℝ → ℂ) : ℝ → ℂ :=
  fun t => Real.exp (t / 2) • f (Real.exp t)

/-- Derivative of the log-substituted function: for smooth `f`,
`(U f)'(t) = e^{t/2} ((1/2) f(e^t) + e^t f'(e^t))`. -/
theorem hasDerivAt_logSubst (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) :
    HasDerivAt (logSubst f)
      ((Real.exp (t / 2) : ℂ) *
        ((1 / 2) * f (Real.exp t) + (Real.exp t : ℂ) * deriv f (Real.exp t))) t := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (s / 2)) (Real.exp (t / 2) * (1 / 2)) t := by
    simpa using (Real.hasDerivAt_exp (t / 2)).comp t ((hasDerivAt_id t).div_const 2)
  have h1 : HasDerivAt (fun s : ℝ => ((Real.exp (s / 2) : ℝ) : ℂ))
      ((Real.exp (t / 2) * (1 / 2) : ℝ) : ℂ) t := he.ofReal_comp
  have h2 : HasDerivAt (fun s : ℝ => f (Real.exp s)) (Real.exp t • deriv f (Real.exp t)) t :=
    (((hf.differentiable (by simp)).differentiableAt (x := Real.exp t)).hasDerivAt).scomp t
      (Real.hasDerivAt_exp t)
  have hmul := h1.mul h2
  simp only [Complex.real_smul] at hmul ⊢
  convert hmul using 1
  push_cast
  ring

/-- **Conjugation to momentum.**  Under the logarithmic substitution `(U f)(t) = e^{t/2} f(e^t)`,
the dilation generator `A f = i ((1/2) f + x f')` transports to the momentum operator
`i · d/dt`: pointwise, for every `t : ℝ`,

`U (A f) t = i · (U f)' t`.

This is the pointwise intertwining identity only; no operator-level (essential self-adjointness)
claim is made here.

The hypotheses `hsupp` (compact support) and `hpos` (support inside `(0, ∞)`) are part of the
requested statement of the core, but are not needed for this pointwise identity; only smoothness
of `f` is used. -/
theorem conjugation_to_momentum (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hsupp : HasCompactSupport f) (hpos : tsupport f ⊆ Set.Ioi (0 : ℝ)) (t : ℝ) :
    Real.exp (t / 2) •
        (Complex.I * ((1 / 2) * f (Real.exp t) + (Real.exp t : ℂ) * deriv f (Real.exp t)))
      = Complex.I * deriv (fun s : ℝ => Real.exp (s / 2) • f (Real.exp s)) t := by
  have key := hasDerivAt_logSubst f hf t
  rw [show (fun s : ℝ => Real.exp (s / 2) • f (Real.exp s)) = logSubst f from rfl, key.deriv]
  simp only [Complex.real_smul]
  ring

end DilationGenerator
end Brockian
#print axioms Brockian.DilationGenerator.conjugation_to_momentum

