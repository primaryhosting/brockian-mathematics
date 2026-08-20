/-
# Canonical Commutator
Category: Quantum Physics
Target: QPhys.canonical_commutator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Canonical Commutator
Category: Quantum Physics
Target: QPhys.canonical_commutator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

open Complex SchwartzMap

/-- The position operator `X`, acting on complex-valued functions of a real variable
by multiplication with the coordinate: `(X f)(x) = x * f(x)`. -/

theorem hasDerivAt_posOp (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    HasDerivAt (posOp (f : ℝ → ℂ)) (f x + (x : ℂ) * deriv (f : ℝ → ℂ) x) x := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (f : ℝ → ℂ) (deriv (f : ℝ → ℂ) x) x :=
    (f.differentiable x).hasDerivAt
  have := h1.mul h2
  simpa [posOp, one_mul] using this

