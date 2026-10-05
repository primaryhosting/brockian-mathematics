import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real

namespace Frontier

/-! ## The finite-volume 2D Ising model on an `L × L` torus -/

/-- Shift a periodic (torus) index by one site. -/

noncomputable def logZDensity (L : ℕ) (K : ℝ) : ℝ := (1 / (L : ℝ) ^ 2) * Real.log (isingZ L K)

/-! ## Onsager's exact formula -/

/-- The integrand of Onsager's formula:
`log (cosh²(2K) - sinh(2K)(cos θ + cos φ))`. -/
