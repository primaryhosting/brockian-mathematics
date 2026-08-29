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

open Complex

/-- The position operator `x̂`, acting on a function `ℝ → ℂ` by pointwise multiplication
by the (complexified) coordinate. -/

lemma deriv_posOp (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    deriv (posOp (f : ℝ → ℂ)) x = f x + (x : ℂ) * deriv (f : ℝ → ℂ) x := by
  have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
    simpa using Complex.ofRealCLM.hasDerivAt (x := x)
  have h2 : HasDerivAt (f : ℝ → ℂ) (deriv (f : ℝ → ℂ) x) x :=
    (SchwartzMap.differentiable f x).hasDerivAt
  have := h1.mul h2
  simpa [posOp, mul_comm, add_comm] using this.deriv

/-- **Canonical commutation relation.** For every Schwartz function `f : 𝓢(ℝ, ℂ)`, with the
position operator `x̂ f = x · f` and the momentum operator `p̂ = -i ℏ d/dx`, one has
`[x̂, p̂] f = i ℏ f` pointwise. -/
