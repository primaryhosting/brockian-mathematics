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

theorem paradoxical_ball : Paradoxical (E ≃ᵢ E) (closedBall (0 : E) 1) := by
  have h : Paradoxical (E ≃ᵢ E) (closedBall (0 : E) 1 \ {0}) :=
    paradoxical_punctured_ball.map toIso (fun g x => rfl)
  exact h.of_equidec equidec_ball_punctured.symm

end BT

/-
The Hausdorff paradox: the unit sphere in `ℝ³` is paradoxical for the action of the group of
linear isometries.
-/
import RequestProject.BT.Equidec
import RequestProject.BT.FreeRotations
import RequestProject.BT.FixedPoints
import RequestProject.BT.FreeGroupParadox
import RequestProject.BT.AbsorbAngles

open Set Function
open scoped Pointwise

namespace BT

/-- The unit sphere of `ℝ³`. -/
