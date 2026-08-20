import RequestProject.BT.Ball

/-!
# Banach Tarski
Category: Frontier — Set Theory
Target: Frontier.Banach_Tarski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Metric Set
open scoped Pointwise

namespace Frontier

/-- The vector by which the second copy of the ball is translated. -/

theorem countable_smul_set (g : E ≃ₗᵢ[ℝ] E) {D : Set E} (hD : D.Countable) :
    (g • D).Countable := hD.image _

/-- A rotation whose iterates move a countable subset of the unit sphere off itself. -/
