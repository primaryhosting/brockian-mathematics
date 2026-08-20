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

theorem image (h : Equidec G A B) (hA : A₁ ⊆ A) :
    ∃ B₁ ⊆ B, Equidec G A₁ B₁ ∧ Equidec G (A \ A₁) (B \ B₁) := by
  obtain ⟨f, S, hbij, hdec⟩ := h
  refine ⟨f '' A₁, hbij.image_eq ▸ Set.image_mono hA, ⟨f, S, (hbij.injOn.mono hA).bijOn_image,
    hdec.mono hA fun _ _ => rfl⟩, ⟨f, S, ?_, hdec.mono Set.diff_subset fun _ _ => rfl⟩⟩
  have : f '' (A \ A₁) = B \ f '' A₁ := by
    rw [← hbij.image_eq, Set.image_diff_of_injOn hbij.injOn hA]
  rw [← this]
  exact (hbij.injOn.mono Set.diff_subset).bijOn_image

