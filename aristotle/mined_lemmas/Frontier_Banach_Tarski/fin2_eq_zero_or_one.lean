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

theorem fin2_eq_zero_or_one (i : Fin 2) : i = 0 ∨ i = 1 := by omega

/-- **The key arithmetic lemma**: for a nonempty reduced word the middle coordinate is never
divisible by three. -/
