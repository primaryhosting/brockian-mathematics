/-
# Canonical Commutator
Category: Quantum Physics
Target: QPhys.canonical_commutator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

open Complex

/-- The position operator `X : f ↦ (x ↦ x · f x)` acting on complex-valued
functions of a real variable. -/

lemma hasDerivAt_schwartz_mul (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => f y * (y : ℂ)) (deriv (⇑f) x * x + f x) x := by
  have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x))
  have h2 : HasDerivAt (⇑f) (deriv (⇑f) x) x := (f.differentiable x).hasDerivAt
  simpa [mul_one] using h2.mul h1

/-- **Canonical commutation relation, operator form.** As continuous linear
operators on Schwartz space, `[posCLM, momCLM ℏ] = i ℏ • id`. -/
