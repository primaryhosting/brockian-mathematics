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

theorem union_piece_zero_smul :
    piece 0 ∪ (FreeGroup.of (0 : Fin 2) • piece 1) = Set.univ := by
  ext w
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  by_cases hw : w ∈ piece 0
  · exact Or.inl hw
  · right
    rw [mem_piece_zero] at hw
    push_neg at hw
    obtain ⟨h1, h2⟩ := hw
    rw [mem_smul_iff, mem_piece_one, toWord_inv_of_mul, if_neg h1]
    refine ⟨by simp, ?_⟩
    rintro ⟨n, hn, hrep⟩
    rw [toWord_inv_of_mul, if_neg h1] at hrep
    cases n with
    | zero => simp at hn
    | succ m =>
      rw [List.replicate_succ] at hrep
      exact h2 ⟨m, by simpa using hrep⟩

