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

theorem conjugation_to_momentum (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hsupp : HasCompactSupport f) (hpos : tsupport f ⊆ Set.Ioi (0 : ℝ)) (t : ℝ) :
    Real.exp (t / 2) • (Complex.I * ((1 / 2) * f (Real.exp t)
        + Real.exp t * deriv f (Real.exp t)))
      = Complex.I * deriv (fun s => Real.exp (s / 2) • f (Real.exp s)) t := by
  have hd : DifferentiableAt ℝ f (Real.exp t) :=
    (hf.differentiable (by norm_num)) (Real.exp t)
  have h := (hasDerivAt_logSubst f t hd).deriv
  show Real.exp (t / 2) • (Complex.I * _) = Complex.I * deriv (logSubst f) t
  rw [h]
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

