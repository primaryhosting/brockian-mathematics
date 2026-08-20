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

theorem phi_free {w : FreeGroup (Fin 2)} {x : E} (hx : x ∈ SX) (h : phi w x = x) : w = 1 := by
  by_contra hw
  exact hx.2 ⟨hx.1, w, hw, h⟩

section Selector

/-- The orbit equivalence of the free group action on `SX`. -/
