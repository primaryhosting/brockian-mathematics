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

noncomputable def genR (x : Fin 2 × Bool) : E ≃ₗᵢ[ℝ] E :=
  cond x.2 (![rotA, rotB] x.1) (![rotA, rotB] x.1)⁻¹

