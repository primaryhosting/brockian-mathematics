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

noncomputable def isingZ (L : ℕ) (K : ℝ) : ℝ := ∑ σ : Config L, Real.exp (K * bondSum σ)

/-- The finite-volume free-energy density `(1/L²) log Z_L(K)`
(i.e. `-β f_L`, the reduced free energy per site). -/
