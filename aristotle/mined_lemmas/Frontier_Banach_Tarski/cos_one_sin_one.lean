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

theorem cos_one_sin_one : Real.cos 1 ^ 2 + Real.sin 1 ^ 2 = 1 := Real.cos_sq_add_sin_sq 1

/-- The rotation by one radian about the vertical axis through `pHalf`. -/
