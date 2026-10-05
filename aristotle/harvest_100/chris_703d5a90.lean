/-
# Conjugation To Momentum
Category: Gate1 Operator
Target: Brockian.DilationGenerator.conjugation_to_momentum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Conjugation To Momentum
Category: Gate1 Operator
Target: Brockian.DilationGenerator.conjugation_to_momentum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Brockian.DilationGenerator

/--
**Conjugation of the dilation generator to the momentum operator (pointwise form).**

Let `U` be the log substitution `(U f) t = e^{t/2} • f (e^t)` and let
`A f = i ((1/2) f + x f')` be the dilation generator on `(0, ∞)`.  Then, pointwise in `t`,
`U (A f) t = i * (U f)' t`, i.e. `A = U⁻¹ ∘ (i · d/dt) ∘ U` on the core.

The hypotheses `hsupp` and `hpos` (compact support contained in `(0, ∞)`) are stated because
they are part of the intended core of the operator, but they are not needed for this pointwise
identity: smoothness of `f` alone suffices.  This is a pointwise intertwining identity only;
no operator-level (essential self-adjointness) claim is made.
-/
theorem conjugation_to_momentum
    (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hsupp : HasCompactSupport f) (hpos : tsupport f ⊆ Set.Ioi (0 : ℝ)) (t : ℝ) :
    Real.exp (t / 2) •
        (Complex.I *
          ((1 / 2) * f (Real.exp t) + Real.exp t * deriv f (Real.exp t))) =
      Complex.I * deriv (fun s => Real.exp (s / 2) • f (Real.exp s)) t := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  -- derivative of `s ↦ e^{s/2}` (viewed in `ℂ`)
  have hu : HasDerivAt (fun s : ℝ => ((Real.exp (s / 2) : ℝ) : ℂ))
      (((1 / 2 * Real.exp (t / 2) : ℝ) : ℂ)) t := by
    have h : HasDerivAt (fun s : ℝ => Real.exp (s / 2)) (Real.exp (t / 2) * (1 / 2)) t := by
      simpa using (Real.hasDerivAt_exp (t / 2)).comp t ((hasDerivAt_id t).div_const 2)
    simpa [mul_comm] using h.ofReal_comp
  -- derivative of `s ↦ f (e^s)` by the chain rule
  have hv : HasDerivAt (fun s : ℝ => f (Real.exp s)) ((Real.exp t : ℝ) • deriv f (Real.exp t)) t :=
    ((hfd (Real.exp t)).hasDerivAt).scomp t (Real.hasDerivAt_exp t)
  -- product rule
  have hg : HasDerivAt (fun s : ℝ => Real.exp (s / 2) • f (Real.exp s))
      (((1 / 2 * Real.exp (t / 2) : ℝ) : ℂ) * f (Real.exp t)
        + ((Real.exp (t / 2) : ℝ) : ℂ) * ((Real.exp t : ℝ) • deriv f (Real.exp t))) t := by
    simpa [Complex.real_smul] using hu.mul hv
  rw [hg.deriv]
  push_cast [Complex.real_smul]
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

