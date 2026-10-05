/-
# Asymptotic Freedom Sign
Category: Frontier Physics
Target: Frontier.asymptotic_freedom_sign
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- The one-loop coefficient `b₀ = (11 N - 2 n_f)/3` of the SU(N) gauge beta function,
with `N` colours and `n_f` Dirac fermion flavours in the fundamental representation. -/

noncomputable def oneLoopBeta (N nf : ℕ) (g : ℝ) : ℝ :=
  -betaZeroCoeff N nf * g ^ 3 / (16 * Real.pi ^ 2)

/-- **Asymptotic freedom sign.** For an SU(N) gauge theory with `n_f` fermion flavours
satisfying the asymptotic-freedom condition `2 n_f < 11 N`, the one-loop beta function
is strictly negative at any positive coupling `g`. -/
