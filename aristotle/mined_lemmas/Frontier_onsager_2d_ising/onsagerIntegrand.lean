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

noncomputable def onsagerIntegrand (K θ φ : ℝ) : ℝ :=
  Real.log (Real.cosh (2 * K) ^ 2 - Real.sinh (2 * K) * (Real.cos θ + Real.cos φ))

/-- Onsager's exact reduced free energy per site:
`log 2 + (1/2)(2π)⁻² ∫₀^{2π}∫₀^{2π} log (cosh²(2K) - sinh(2K)(cos θ + cos φ)) dθ dφ`. -/
