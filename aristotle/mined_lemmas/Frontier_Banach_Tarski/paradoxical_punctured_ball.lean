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

theorem paradoxical_punctured_ball :
    Paradoxical (E ≃ₗᵢ[ℝ] E) (closedBall (0 : E) 1 \ {0}) := by
  obtain ⟨A₁, A₂, hunion, hdisj, h₁, h₂⟩ := paradoxical_S2
  have hA₁ : A₁ ⊆ S2 := hunion ▸ Set.subset_union_left
  have hA₂ : A₂ ⊆ S2 := hunion ▸ Set.subset_union_right
  refine ⟨star A₁, star A₂, ?_, star_disjoint hdisj, ?_, ?_⟩
  · rw [← star_union, hunion, star_S2]
  · rw [← star_S2]; exact star_equidec hA₁ (fun _ h => h) h₁
  · rw [← star_S2]; exact star_equidec hA₂ (fun _ h => h) h₂

section Center

/-- The point about whose vertical axis we rotate in order to absorb the centre of the ball. -/
