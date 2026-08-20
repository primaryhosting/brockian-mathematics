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

def stp (l : Fin 2 × Bool) (v : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  if l.1 = 0 then (v.1 - 2 * sgnZ l.2 * v.2.1, v.2.1 + 4 * sgnZ l.2 * v.1, 3 * v.2.2)
  else (3 * v.1, v.2.1 - 4 * sgnZ l.2 * v.2.2, v.2.2 + 2 * sgnZ l.2 * v.2.1)

/-- The integer triple attached to a word. -/
