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

theorem phi_mk (L : List (Fin 2 × Bool)) : phi (FreeGroup.mk L) = (L.map genR).prod :=
  FreeGroup.lift_mk

