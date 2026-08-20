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

theorem cos_sin_one_third : (1 / 3 : ℝ) ^ 2 + (2 * Real.sqrt 2 / 3) ^ 2 = 1 := by
  have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [h]

/-- Rotation about the `z`-axis by the angle `arccos (1/3)`. -/
