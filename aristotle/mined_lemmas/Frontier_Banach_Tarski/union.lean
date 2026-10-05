import RequestProject.Equidecomp

/-!
# Rotations of `ℝ³`

Set-up for the Banach–Tarski paradox: the group `SO(3)` of rotations acting on
`E = EuclideanSpace ℝ (Fin 3)`, the group of isometries of `E`, and the fact that a
non-identity rotation fixes at most two points of the unit sphere.
-/

open Matrix

namespace BanachTarski

/-- Three dimensional Euclidean space. -/
abbrev E := EuclideanSpace ℝ (Fin 3)

/-- The group of rotations of `ℝ³`. -/
abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

noncomputable instance : SMul ↥SO3 E :=
  ⟨fun M x => WithLp.toLp 2 ((M : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ WithLp.ofLp x)⟩


theorem union {A₁ A₂ B₁ B₂ : Set X} (h₁ : Equidecomp G A₁ B₁) (h₂ : Equidecomp G A₂ B₂)
    (hA : Disjoint A₁ A₂) (hB : Disjoint B₁ B₂) :
    Equidecomp G (A₁ ∪ A₂) (B₁ ∪ B₂) := by
  classical
  obtain ⟨f₁, S₁, hS₁, hb₁, hs₁⟩ := h₁
  obtain ⟨f₂, S₂, hS₂, hb₂, hs₂⟩ := h₂
  refine ⟨fun x => if x ∈ A₁ then f₁ x else f₂ x, S₁ ∪ S₂, hS₁.union hS₂, ⟨?_, ?_, ?_⟩, ?_⟩
  · rintro x (hx | hx)
    · simp only [if_pos hx]; exact Or.inl (hb₁.mapsTo hx)
    · have hx1 : x ∉ A₁ := fun h => Set.disjoint_left.mp hA h hx
      simp only [if_neg hx1]; exact Or.inr (hb₂.mapsTo hx)
  · rintro x hx y hy hxy
    have hx' : x ∈ A₁ ∨ (x ∉ A₁ ∧ x ∈ A₂) := by
      rcases hx with h | h
      · exact Or.inl h
      · by_cases h1 : x ∈ A₁
        · exact Or.inl h1
        · exact Or.inr ⟨h1, h⟩
    have hy' : y ∈ A₁ ∨ (y ∉ A₁ ∧ y ∈ A₂) := by
      rcases hy with h | h
      · exact Or.inl h
      · by_cases h1 : y ∈ A₁
        · exact Or.inl h1
        · exact Or.inr ⟨h1, h⟩
    rcases hx' with hx1 | ⟨hx1, hx2⟩ <;> rcases hy' with hy1 | ⟨hy1, hy2⟩
    · simp only [if_pos hx1, if_pos hy1] at hxy; exact hb₁.injOn hx1 hy1 hxy
    · simp only [if_pos hx1, if_neg hy1] at hxy
      exact absurd (by rw [hxy]; exact hb₂.mapsTo hy2 : f₁ x ∈ B₂)
        (Set.disjoint_left.mp hB (hb₁.mapsTo hx1))
    · simp only [if_neg hx1, if_pos hy1] at hxy
      exact absurd (by rw [hxy]; exact hb₁.mapsTo hy1 : f₂ x ∈ B₁)
        (Set.disjoint_right.mp hB (hb₂.mapsTo hx2))
    · simp only [if_neg hx1, if_neg hy1] at hxy; exact hb₂.injOn hx2 hy2 hxy
  · rintro y (hy | hy)
    · obtain ⟨x, hx, rfl⟩ := hb₁.surjOn hy
      exact ⟨x, Or.inl hx, by simp [if_pos hx]⟩
    · obtain ⟨x, hx, rfl⟩ := hb₂.surjOn hy
      have hx1 : x ∉ A₁ := fun h => Set.disjoint_left.mp hA h hx
      exact ⟨x, Or.inr hx, by simp [if_neg hx1]⟩
  · rintro x (hx | hx)
    · obtain ⟨g, hg, hgx⟩ := hs₁ x hx
      exact ⟨g, Or.inl hg, by simpa [if_pos hx] using hgx⟩
    · have hx1 : x ∉ A₁ := fun h => Set.disjoint_left.mp hA h hx
      obtain ⟨g, hg, hgx⟩ := hs₂ x hx
      exact ⟨g, Or.inr hg, by simpa [if_neg hx1] using hgx⟩

/-- A set is equidecomposable with any translate of itself. -/
