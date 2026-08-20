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

theorem Wstart_disjoint {x y : Fin 2 × Bool} (hxy : x ≠ y) : Disjoint (Wstart x) (Wstart y) := by
  rw [Set.disjoint_left]
  intro w hx hy
  rw [mem_Wstart] at hx hy
  exact hxy (Option.some_injective _ (hx.symm.trans hy))

