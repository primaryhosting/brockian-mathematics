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

theorem of_equidec [Nonempty X] (hP : Paradoxical G A) (h : Equidec G A B) :
    Paradoxical G B := by
  obtain ⟨A₁, A₂, hunion, hdisj, h₁, h₂⟩ := hP
  obtain ⟨B₁, hB₁sub, hb₁, hb₂⟩ := h.image (hunion ▸ Set.subset_union_left (t := A₂))
  refine ⟨B₁, B \ B₁, by simp [hB₁sub], disjoint_sdiff_right,
    (hb₁.symm.trans h₁).trans h, ?_⟩
  have hAA : A \ A₁ = A₂ := by
    rw [← hunion]
    ext x
    constructor
    · rintro ⟨hx | hx, hx'⟩
      · exact absurd hx hx'
      · exact hx
    · intro hx
      exact ⟨Or.inr hx, fun h => (hdisj.le_bot ⟨h, hx⟩).elim⟩
  rw [hAA] at hb₂
  exact (hb₂.symm.trans h₂).trans h

/-- If `A` is paradoxical and `B` is a disjoint congruent copy of `A`, then `A` is
equidecomposable with `A ∪ B`: `A` can be doubled. -/
