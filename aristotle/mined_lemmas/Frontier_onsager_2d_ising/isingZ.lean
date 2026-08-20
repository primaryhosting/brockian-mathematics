/-
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Real

namespace Frontier

/-- A Boolean spin variable read as a real number `±1`. -/

noncomputable def isingZ (n : ℕ) (K : ℝ) : ℝ :=
  ∑ σ : ZMod (n + 1) × ZMod (n + 1) → Bool, Real.exp (K * isingEnergy n σ)

/-- The argument of the logarithm in Onsager's exact solution:
`cosh²(2K) - sinh(2K)(cos θ₁ + cos θ₂)`. -/
