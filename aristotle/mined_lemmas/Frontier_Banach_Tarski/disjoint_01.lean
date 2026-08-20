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

theorem disjoint_01 : Disjoint (piece 0) (piece 1) := by
  rw [Set.disjoint_left]
  intro w h1 h2
  rw [mem_piece_zero] at h1
  rw [mem_piece_one] at h2
  rcases h1 with h | h
  · exact absurd (Option.some_injective _ (h.symm.trans h2.1)) (by simp)
  · obtain ⟨n, hn⟩ := h
    refine h2.2 ⟨n, ?_, hn⟩
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [List.replicate_zero] at hn
      rw [hn] at h2
      simp at h2
    · exact hpos

