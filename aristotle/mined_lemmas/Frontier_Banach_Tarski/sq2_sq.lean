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

theorem sq2_sq : sq2 * sq2 = 2 := by
  rw [sq2]
  exact Real.mul_self_sqrt (by norm_num)

/-- The sign attached to a letter: `+1` for a generator, `-1` for its inverse. -/
