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

theorem disjoint_piece_two_smul : Disjoint (piece 2) (FreeGroup.of (1 : Fin 2) • piece 3) := by
  rw [Set.disjoint_left]
  intro w hw hmem
  rw [mem_smul_iff, mem_piece_three, toWord_inv_of_mul] at hmem
  have h : w.toWord.head? = some ((1 : Fin 2), true) := mem_piece_two.1 hw
  rw [if_pos h] at hmem
  exact tail_head?_ne h (by simpa using hmem)

