/-
# Asymptotic Freedom Sign
Category: Frontier Physics
Target: Frontier.asymptotic_freedom_sign
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Asymptotic Freedom Sign
Category: Frontier Physics
Target: Frontier.asymptotic_freedom_sign
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Real

/-- The one-loop beta-function coefficient `b₀` for an `SU(N)` gauge theory with
`Nf` Dirac fermions in the fundamental representation:
`b₀ = 11 N / 3 - 2 Nf / 3`. -/

noncomputable def betaZero (N Nf : ℕ) : ℝ := 11 * (N : ℝ) / 3 - 2 * (Nf : ℝ) / 3

/-- The one-loop beta function of an `SU(N)` gauge theory with `Nf` fundamental Dirac
fermions, as a function of the gauge coupling `g`:
`β(g) = - b₀ g³ / (16 π²)`. -/
