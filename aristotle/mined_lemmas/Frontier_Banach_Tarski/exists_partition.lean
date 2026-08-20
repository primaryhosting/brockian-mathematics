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

theorem exists_partition (h : Equidec G A B) :
    ∃ (n : ℕ) (P : Fin n → Set X) (g : Fin n → G),
      (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧ (⋃ i, P i) = A ∧
      (∀ i j, i ≠ j → Disjoint (g i • P i) (g j • P j)) ∧ (⋃ i, g i • P i) = B := by
  classical
  obtain ⟨f, S, hbij, hdec⟩ := h
  -- choose, for each point of `A`, a group element realizing `f` there
  choose! γ hγS hγ using hdec
  set e : Fin S.card ≃ {x // x ∈ S} := S.equivFin.symm with he
  refine ⟨S.card, fun i => {a ∈ A | γ a = (e i : G)}, fun i => (e i : G), ?_, ?_, ?_, ?_⟩
  · intro i j hij
    refine Set.disjoint_left.2 ?_
    rintro a ⟨-, ha⟩ ⟨-, ha'⟩
    exact hij (e.injective (Subtype.ext (ha ▸ ha')))
  · ext a
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, ha, -⟩; exact ha
    · intro ha
      exact ⟨e.symm ⟨γ a, hγS a ha⟩, ha, by simp⟩
  · have himg : ∀ i : Fin S.card, ((e i : G)) • {a ∈ A | γ a = (e i : G)}
        = f '' {a ∈ A | γ a = (e i : G)} := by
      intro i
      ext y
      constructor
      · rintro ⟨a, ⟨ha, ha'⟩, rfl⟩
        exact ⟨a, ⟨ha, ha'⟩, by rw [hγ a ha, ha']⟩
      · rintro ⟨a, ⟨ha, ha'⟩, rfl⟩
        exact ⟨a, ⟨ha, ha'⟩, by rw [hγ a ha, ha']⟩
    intro i j hij
    rw [himg i, himg j]
    refine Set.disjoint_left.2 ?_
    rintro y ⟨a, ⟨ha, ha'⟩, rfl⟩ ⟨b, ⟨hb, hb'⟩, hb''⟩
    have : b = a := hbij.injOn hb ha hb''
    subst this
    exact hij (e.injective (Subtype.ext (ha'.symm.trans hb')))
  · have himg : ∀ i : Fin S.card, ((e i : G)) • {a ∈ A | γ a = (e i : G)}
        = f '' {a ∈ A | γ a = (e i : G)} := by
      intro i
      ext y
      constructor
      · rintro ⟨a, ⟨ha, ha'⟩, rfl⟩
        exact ⟨a, ⟨ha, ha'⟩, by rw [hγ a ha, ha']⟩
      · rintro ⟨a, ⟨ha, ha'⟩, rfl⟩
        exact ⟨a, ⟨ha, ha'⟩, by rw [hγ a ha, ha']⟩
    ext y
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hy⟩
      rw [himg i] at hy
      obtain ⟨a, ⟨ha, -⟩, rfl⟩ := hy
      exact hbij.mapsTo ha
    · intro hy
      obtain ⟨a, ha, rfl⟩ := hbij.surjOn hy
      refine ⟨e.symm ⟨γ a, hγS a ha⟩, ?_⟩
      rw [himg]
      exact ⟨a, ⟨ha, by simp⟩, rfl⟩

end Equidec

/-- A set is paradoxical if it can be split into two disjoint pieces, each of which is
equidecomposable with the whole set. -/
