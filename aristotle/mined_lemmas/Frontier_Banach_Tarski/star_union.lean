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

theorem star_union (A B : Set E) : star (A ∪ B) = star A ∪ star B := by
  ext y
  simp only [star, Set.mem_setOf_eq, Set.mem_union]
  tauto

