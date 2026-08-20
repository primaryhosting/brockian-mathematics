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

theorem union (hA : Disjoint A₁ A₂) (hB : Disjoint B₁ B₂)
    (h₁ : Equidec G A₁ B₁) (h₂ : Equidec G A₂ B₂) : Equidec G (A₁ ∪ A₂) (B₁ ∪ B₂) := by
  classical
  obtain ⟨f, S, hbij, hdec⟩ := h₁
  obtain ⟨f', S', hbij', hdec'⟩ := h₂
  have hval : ∀ z ∈ A₁ ∪ A₂, (z ∈ A₁ ∧ Set.piecewise A₁ f f' z = f z) ∨
      (z ∈ A₂ ∧ z ∉ A₁ ∧ Set.piecewise A₁ f f' z = f' z) := by
    rintro z (hz | hz)
    · exact Or.inl ⟨hz, by simp [Set.piecewise, hz]⟩
    · have hz' : z ∉ A₁ := fun h => (hA.le_bot ⟨h, hz⟩).elim
      exact Or.inr ⟨hz, hz', by simp [Set.piecewise, hz']⟩
  refine ⟨Set.piecewise A₁ f f', S ∪ S', ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x hx
    rcases hval x hx with ⟨hx1, hxe⟩ | ⟨hx2, _, hxe⟩
    · exact Or.inl (hxe ▸ hbij.mapsTo hx1)
    · exact Or.inr (hxe ▸ hbij'.mapsTo hx2)
  · intro x hx y hy hxy
    rcases hval x hx with ⟨hx1, hxe⟩ | ⟨hx2, _, hxe⟩ <;>
      rcases hval y hy with ⟨hy1, hye⟩ | ⟨hy2, _, hye⟩
    · exact hbij.injOn hx1 hy1 (by rw [← hxe, ← hye]; exact hxy)
    · refine ((Set.disjoint_left.mp hB (hbij.mapsTo hx1) ?_)).elim
      exact (by rw [← hxe, hxy, hye] : f x = f' y) ▸ hbij'.mapsTo hy2
    · refine ((Set.disjoint_left.mp hB (hbij.mapsTo hy1) ?_)).elim
      exact (by rw [← hye, ← hxy, hxe] : f y = f' x) ▸ hbij'.mapsTo hx2
    · exact hbij'.injOn hx2 hy2 (by rw [← hxe, ← hye]; exact hxy)
  · rintro y (hy | hy)
    · obtain ⟨x, hx, rfl⟩ := hbij.surjOn hy
      exact ⟨x, Or.inl hx, by simp [Set.piecewise, hx]⟩
    · obtain ⟨x, hx, rfl⟩ := hbij'.surjOn hy
      have hx' : x ∉ A₁ := fun h => (hA.le_bot ⟨h, hx⟩).elim
      exact ⟨x, Or.inr hx, by simp [Set.piecewise, hx']⟩
  · rintro a (ha | ha)
    · obtain ⟨g, hg, hga⟩ := hdec a ha
      exact ⟨g, Finset.mem_union_left _ hg, by simpa [Set.piecewise, ha] using hga⟩
    · have ha' : a ∉ A₁ := fun h => (hA.le_bot ⟨h, ha⟩).elim
      obtain ⟨g, hg, hga⟩ := hdec' a ha
      exact ⟨g, Finset.mem_union_right _ hg, by simpa [Set.piecewise, ha'] using hga⟩

/-- An equidecomposition, presented as an explicit finite partition of `A` into pieces which
are moved by single group elements to give a partition of `B`. -/
