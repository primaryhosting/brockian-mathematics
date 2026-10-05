-- (Lean 4 requires `import` lines to precede any command, including module
-- docstrings, so the requested header comment is placed immediately below.)
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

/-- **Conjugation of the dilation generator to the momentum operator (pointwise form).**

For `f : ℝ → ℂ` smooth with compact support contained in `(0, ∞)`, the unitary log
substitution `(U f)(t) = e^{t/2} f(e^t)` intertwines the dilation generator
`A f (x) = i ((1/2) f x + x f' x)` with the momentum operator `i · d/dt`:

`U (A f) t = i · (U f)' t`  for every `t : ℝ`.

This is the pointwise intertwining identity only; no operator-level (essential
self-adjointness) claim is made.

The proof only uses differentiability of `f`; the compact-support hypotheses
`hsupp` and `hpos` are stated because they are part of the intended core of the
operator, but they are not needed for the pointwise identity. -/
theorem conjugation_to_momentum
    (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hsupp : HasCompactSupport f) (hpos : tsupport f ⊆ Set.Ioi (0 : ℝ))
    (t : ℝ) :
    Real.exp (t / 2) •
        (Complex.I *
          ((1 / 2) * f (Real.exp t) + (Real.exp t : ℂ) * deriv f (Real.exp t))) =
      Complex.I * deriv (fun s : ℝ => Real.exp (s / 2) • f (Real.exp s)) t := by
  have hd : HasDerivAt f (deriv f (Real.exp t)) (Real.exp t) :=
    (hf.differentiable (by simp) _).hasDerivAt
  have h1 : HasDerivAt (fun s : ℝ => Real.exp (s / 2)) (Real.exp (t / 2) * (1 / 2)) t :=
    (Real.hasDerivAt_exp _).comp t ((hasDerivAt_id t).div_const 2)
  have h1' : HasDerivAt (fun s : ℝ => ((Real.exp (s / 2) : ℝ) : ℂ))
      ((Real.exp (t / 2) * (1 / 2) : ℝ) : ℂ) t := h1.ofReal_comp
  have h2 : HasDerivAt (fun s : ℝ => f (Real.exp s)) (Real.exp t • deriv f (Real.exp t)) t :=
    hd.scomp t (Real.hasDerivAt_exp t)
  have hg : HasDerivAt (fun s : ℝ => Real.exp (s / 2) • f (Real.exp s))
      (((Real.exp (t / 2) * (1 / 2) : ℝ) : ℂ) * f (Real.exp t)
        + ((Real.exp (t / 2) : ℝ) : ℂ) * (Real.exp t • deriv f (Real.exp t))) t := by
    simpa [Complex.real_smul] using h1'.mul h2
  rw [hg.deriv]
  push_cast [Complex.real_smul]
  ring

end DilationGenerator
end Brockian

