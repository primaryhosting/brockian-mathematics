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

theorem deriv_posOp (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    deriv (posOp (f : ℝ → ℂ)) x = f x + (x : ℂ) * deriv (f : ℝ → ℂ) x :=
  (hasDerivAt_posOp f x).deriv

/-- **Canonical commutation relation.** On Schwartz space, with the momentum operator
`P = -i ℏ d/dx` and the position operator `(X f)(x) = x f(x)`, one has
`[X, P] f = i ℏ f`. -/
