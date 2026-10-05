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


theorem trans {A B C : Set X} (h₁ : Equidecomp G A B) (h₂ : Equidecomp G B C) :
    Equidecomp G A C := by
  obtain ⟨f₁, S₁, hS₁, hb₁, hs₁⟩ := h₁
  obtain ⟨f₂, S₂, hS₂, hb₂, hs₂⟩ := h₂
  refine ⟨f₂ ∘ f₁, S₂ * S₁, hS₂.mul hS₁, hb₂.comp hb₁, ?_⟩
  intro x hx
  obtain ⟨g₁, hg₁, h₁⟩ := hs₁ x hx
  obtain ⟨g₂, hg₂, h₂⟩ := hs₂ (f₁ x) (hb₁.mapsTo hx)
  exact ⟨g₂ * g₁, Set.mul_mem_mul hg₂ hg₁, by
    rw [Function.comp_apply, h₂, h₁, mul_smul]⟩

/-- Equidecomposability of a union of two disjoint pieces. -/
