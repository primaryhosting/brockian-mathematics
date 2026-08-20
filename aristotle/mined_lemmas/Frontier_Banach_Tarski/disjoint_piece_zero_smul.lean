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

theorem disjoint_piece_zero_smul : Disjoint (piece 0) (FreeGroup.of (0 : Fin 2) • piece 1) := by
  rw [Set.disjoint_left]
  intro w hw hmem
  rw [mem_smul_iff] at hmem
  rw [mem_piece_one, toWord_inv_of_mul] at hmem
  rcases mem_piece_zero.1 hw with h | h
  · rw [if_pos h] at hmem
    exact tail_head?_ne h (by simpa using hmem.1)
  · obtain ⟨n, hn⟩ := h
    have hne : w.toWord.head? ≠ some ((0 : Fin 2), true) := by
      intro hc
      have := Nneg_head_eq ⟨n, hn⟩ hc
      simp at this
    rw [if_neg hne] at hmem
    refine hmem.2 ⟨n + 1, Nat.succ_pos n, ?_⟩
    rw [toWord_inv_of_mul, if_neg hne, hn, List.replicate_succ]

