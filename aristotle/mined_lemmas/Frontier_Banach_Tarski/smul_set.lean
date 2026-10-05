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


theorem smul_set (g : G) (A : Set X) : Equidecomp G A (g • A) := by
  refine ⟨fun x => g • x, {g}, Set.finite_singleton _, ⟨?_, ?_, ?_⟩, fun x _ => ⟨g, rfl, rfl⟩⟩
  · intro x hx; exact ⟨x, hx, rfl⟩
  · intro x _ y _ h; exact MulAction.injective g h
  · rintro y ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩

/-- Any part of `A` can be matched with a part of `B`, with matching complements. -/
