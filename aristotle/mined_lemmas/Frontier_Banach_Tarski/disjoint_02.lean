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

theorem disjoint_02 : Disjoint (piece 0) (piece 2) := by
  rw [Set.disjoint_left]
  intro w h1 h2
  rw [mem_piece_zero] at h1
  rw [mem_piece_two] at h2
  rcases h1 with h | h
  · exact absurd (Option.some_injective _ (h.symm.trans h2)) (by simp)
  · have := Nneg_head_eq h h2
    simp at this

