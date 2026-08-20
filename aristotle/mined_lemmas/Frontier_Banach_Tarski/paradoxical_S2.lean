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

theorem paradoxical_S2 : Paradoxical (E ≃ₗᵢ[ℝ] E) S2 :=
  paradoxical_SX.of_equidec equidec_S2_SX.symm

end BT

/-
The set of fixed points on the unit sphere of a linear isometry of `ℝ³` which is not an
involution is countable (in fact it has at most two elements).
-/
import RequestProject.BT.Rotations

open Module

namespace BT

/-- A linear isometry of `ℝ³` whose square is not the identity fixes at most two points of
the unit sphere; in particular its fixed point set on the sphere is countable. -/
