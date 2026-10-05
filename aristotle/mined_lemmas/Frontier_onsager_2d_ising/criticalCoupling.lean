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

noncomputable def criticalCoupling : ℝ := Real.log (1 + Real.sqrt 2) / 2

/-- Onsager's theorem *at a given coupling* `K`: the free-energy density of the finite
torus converges, as the side length tends to infinity, to Onsager's exact expression. -/
