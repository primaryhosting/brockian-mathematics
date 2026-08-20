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

theorem iUnion_piece : (⋃ i, piece i) = Set.univ := by
  ext w
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  rcases head?_cases w with h | ⟨x, hx⟩
  · exact ⟨0, Or.inr ⟨0, by simpa using h⟩⟩
  · obtain ⟨i, b⟩ := x
    fin_cases i
    · cases b
      · by_cases hN : w ∈ Nneg₁
        · exact ⟨0, Or.inr (Nneg₁_subset_Nneg hN)⟩
        · exact ⟨1, ⟨hx, hN⟩⟩
      · exact ⟨0, Or.inl hx⟩
    · cases b
      · exact ⟨3, hx⟩
      · exact ⟨2, hx⟩

