/-
# Canonical Commutator
Category: Quantum Physics
Target: QPhys.canonical_commutator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` because Lean 4 does not allow a
-- module docstring to precede `import`; the exact docstring is repeated below.)

import Mathlib

/-!
# Canonical Commutator
Category: Quantum Physics
Target: QPhys.canonical_commutator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace QPhys

open SchwartzMap

/-- The function `x ↦ (x : ℂ)` has temperate growth (it is a continuous linear map). -/

theorem hasDerivAt_mul_schwartz (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (y : ℂ) * f y) (f x + (x : ℂ) * deriv (⇑f) x) x := by
  have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
  have h2 := f.hasDerivAt x
  simpa using h1.mul h2

/-- **Canonical commutation relation.** On Schwartz space, with the position operator
`X : f ↦ (x ↦ x f x)` and the momentum operator `P = -i ℏ d/dx`, one has
`[X, P] = i ℏ • id`. -/
