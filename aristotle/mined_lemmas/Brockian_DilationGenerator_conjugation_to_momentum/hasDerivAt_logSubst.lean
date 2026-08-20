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
