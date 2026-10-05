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


theorem map {H : Type*} [Group H] [MulAction H X] (σ : G →* H)
    (hσ : ∀ (g : G) (x : X), σ g • x = g • x) {A B : Set X} (h : Equidecomp G A B) :
    Equidecomp H A B := by
  obtain ⟨f, S, hSfin, hbij, hS⟩ := h
  refine ⟨f, σ '' S, hSfin.image _, hbij, fun x hx => ?_⟩
  obtain ⟨g, hg, hgx⟩ := hS x hx
  exact ⟨σ g, ⟨g, hg, rfl⟩, by rw [hσ, hgx]⟩

end Equidecomp

/-- `A` is `G`-paradoxical: it splits into two disjoint pieces, each equidecomposable with
the whole of `A`. -/
