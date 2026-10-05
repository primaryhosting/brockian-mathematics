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

namespace Brockian
namespace DilationGenerator

/-- **Conjugation of the dilation generator to the momentum operator.**

Let `U` be the log substitution `(U f)(t) = e^{t/2} f(e^t)` and let
`A f = i ((1/2) f + x f')` be the (symmetric) dilation generator on `(0, ∞)`.
For `f : ℝ → ℂ` smooth with compact support contained in `(0, ∞)`, the pointwise
intertwining identity `U (A f) = i (U f)'` holds at every `t : ℝ`.

This is the pointwise identity only; no operator-level (essential self-adjointness)
claim is made here.

The hypotheses `hsupp` and `hpos` (compact support inside `(0, ∞)`) are recorded because
they are part of the intended setting, but the pointwise identity does not require them:
smoothness of `f` alone suffices. -/
theorem conjugation_to_momentum
    (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hsupp : HasCompactSupport f) (hpos : tsupport f ⊆ Set.Ioi (0 : ℝ))
    (t : ℝ) :
    Real.exp (t / 2) •
        (Complex.I * ((1 / 2) * f (Real.exp t) + (Real.exp t : ℂ) * deriv f (Real.exp t)))
      = Complex.I * deriv (fun s : ℝ => Real.exp (s / 2) • f (Real.exp s)) t := by
  -- derivative of `s ↦ e^{s/2}`
  have hexp2 : HasDerivAt (fun s : ℝ => Real.exp (s / 2)) (Real.exp (t / 2) * (1 / 2)) t := by
    have h1 : HasDerivAt (fun s : ℝ => s / 2) (1 / 2 : ℝ) t := by
      simpa using (hasDerivAt_id t).div_const 2
    simpa using (Real.hasDerivAt_exp (t / 2)).comp t h1
  have hexpC : HasDerivAt (fun s : ℝ => ((Real.exp (s / 2) : ℝ) : ℂ))
      (((Real.exp (t / 2) * (1 / 2) : ℝ) : ℂ)) t := hexp2.ofReal_comp
  -- chain rule for `s ↦ f (e^s)`
  have hfd : HasDerivAt f (deriv f (Real.exp t)) (Real.exp t) :=
    ((hf.differentiable (by simp)).differentiableAt).hasDerivAt
  have hcomp : HasDerivAt (fun s : ℝ => f (Real.exp s))
      (Real.exp t • deriv f (Real.exp t)) t :=
    HasDerivAt.scomp t hfd (Real.hasDerivAt_exp t)
  -- product rule
  have hprod : HasDerivAt (fun s : ℝ => ((Real.exp (s / 2) : ℝ) : ℂ) * f (Real.exp s))
      (((Real.exp (t / 2) * (1 / 2) : ℝ) : ℂ) * f (Real.exp t)
        + ((Real.exp (t / 2) : ℝ) : ℂ) * (Real.exp t • deriv f (Real.exp t))) t :=
    hexpC.mul hcomp
  have heq : (fun s : ℝ => Real.exp (s / 2) • f (Real.exp s))
      = fun s : ℝ => ((Real.exp (s / 2) : ℝ) : ℂ) * f (Real.exp s) := by
    funext s; exact Complex.real_smul
  rw [heq, hprod.deriv]
  push_cast [Complex.real_smul]
  ring

end DilationGenerator
end Brockian

