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

def OnsagerHoldsAt (K : ℝ) : Prop :=
  Filter.Tendsto (fun L : ℕ => logZDensity L K) Filter.atTop (nhds (onsagerLogZDensity K))

/-- The full statement of Onsager's solution of the 2D square-lattice Ising model. -/
