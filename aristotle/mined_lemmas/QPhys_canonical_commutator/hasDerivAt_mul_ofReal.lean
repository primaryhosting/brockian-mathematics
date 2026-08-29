import Mathlib

/-!
# Canonical Commutator
Category: Quantum Physics
Target: QPhys.canonical_commutator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

open SchwartzMap Complex

/-- The position operator `X : f ↦ (x ↦ x * f x)` as a continuous linear operator on the
Schwartz space `𝓢(ℝ, ℂ)`. -/

theorem hasDerivAt_mul_ofReal (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (y : ℂ) * f y) (f x + (x : ℂ) * deriv f x) x := by
  have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x))
  simpa [one_mul] using h1.mul (f.hasDerivAt x)

/-- **Canonical commutation relation** on Schwartz space: with the position operator
`x` and the momentum operator `p = -i ℏ d/dx`, one has `[x, p] = i ℏ`. -/
