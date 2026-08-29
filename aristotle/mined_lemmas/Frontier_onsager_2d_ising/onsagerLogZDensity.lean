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

noncomputable def onsagerLogZDensity (K : ℝ) : ℝ :=
  Real.log 2 + (1 / 2) * (1 / (2 * π) ^ 2) *
    ∫ θ in (0:ℝ)..(2 * π), ∫ φ in (0:ℝ)..(2 * π), onsagerIntegrand K θ φ

/-- Onsager's critical coupling `K_c = ½ log (1 + √2)`, the unique `K ≥ 0` at which
the argument of the Onsager logarithm vanishes (at `θ = φ = 0`). -/
