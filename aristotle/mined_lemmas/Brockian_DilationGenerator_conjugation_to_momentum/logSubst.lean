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

noncomputable def logSubst (f : ℝ → ℂ) : ℝ → ℂ :=
  fun t => Real.exp (t / 2) • f (Real.exp t)

/-- Core computation: if `f` is differentiable at `e^t`, then `U f` is differentiable at `t`
with derivative `e^{t/2} ((1/2) f (e^t) + e^t f' (e^t))`. -/
