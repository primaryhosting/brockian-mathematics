import Mathlib

/-!
# Conjugation To Momentum
Category: Gate1 Operator
Target: Brockian.DilationGenerator.conjugation_to_momentum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace DilationGenerator

/-- **Conjugation of the dilation generator to the momentum operator (pointwise form).**

Under the logarithmic substitution `(U f)(t) = e^{t/2} f(e^t)`, the dilation generator
`A f = i ((1/2) f + x f')` transports to the momentum operator `i d/dt`:
for every `t : ℝ`,
`e^{t/2} • (i ((1/2) f(e^t) + e^t f'(e^t))) = i · (U f)'(t)`.

This is the pointwise intertwining identity `U ∘ A = (i d/dt) ∘ U` on the core; no
operator-level (essential self-adjointness) claim is made here.

The hypotheses `hsupp` (compact support) and `hpos` (support inside `(0, ∞)`) are stated
because they are part of the intended core of the operator, but they are not needed for
the pointwise identity: differentiability of `f` at `e^t`, which follows from smoothness,
suffices. -/
theorem conjugation_to_momentum
    (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hsupp : HasCompactSupport f) (hpos : tsupport f ⊆ Set.Ioi (0 : ℝ))
    (t : ℝ) :
    Real.exp (t / 2) •
        (Complex.I * ((1 / 2) * f (Real.exp t)
          + (Real.exp t : ℂ) * deriv f (Real.exp t)))
      = Complex.I * deriv (fun s : ℝ => Real.exp (s / 2) • f (Real.exp s)) t := by
  have hg : HasDerivAt (fun s : ℝ => ((Real.exp (s / 2) : ℝ) : ℂ))
      ((Real.exp (t / 2) * (1 / 2) : ℝ) : ℂ) t := by
    have h : HasDerivAt (fun s : ℝ => Real.exp (s / 2)) (Real.exp (t / 2) * (1 / 2)) t := by
      simpa using (Real.hasDerivAt_exp (t / 2)).comp t ((hasDerivAt_id t).div_const 2)
    exact h.ofReal_comp
  have hfd : HasDerivAt f (deriv f (Real.exp t)) (Real.exp t) :=
    ((hf.differentiable (by simp)).differentiableAt).hasDerivAt
  have hcomp : HasDerivAt (fun s : ℝ => f (Real.exp s))
      (Real.exp t • deriv f (Real.exp t)) t := hfd.scomp t (Real.hasDerivAt_exp t)
  have hprod : HasDerivAt (fun s : ℝ => ((Real.exp (s / 2) : ℝ) : ℂ) * f (Real.exp s))
      (((Real.exp (t / 2) * (1 / 2) : ℝ) : ℂ) * f (Real.exp t)
        + ((Real.exp (t / 2) : ℝ) : ℂ) * (Real.exp t • deriv f (Real.exp t))) t := hg.mul hcomp
  have heq : (fun s : ℝ => Real.exp (s / 2) • f (Real.exp s))
      = fun s : ℝ => ((Real.exp (s / 2) : ℝ) : ℂ) * f (Real.exp s) := by
    funext s; simp [Complex.real_smul]
  rw [heq, hprod.deriv]
  push_cast [Complex.real_smul]
  ring

end DilationGenerator
end Brockian

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

