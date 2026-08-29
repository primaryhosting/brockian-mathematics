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


theorem subset_image {A B W : Set X} (h : Equidecomp G A B) (hW : W ⊆ A) :
    ∃ B' ⊆ B, Equidecomp G W B' ∧ Equidecomp G (A \ W) (B \ B') := by
  obtain ⟨f, S, hSfin, hbij, hS⟩ := h
  refine ⟨f '' W, ?_, ⟨f, S, hSfin, ⟨Set.mapsTo_image f W, hbij.injOn.mono hW, ?_⟩,
      fun x hx => hS x (hW hx)⟩, ⟨f, S, hSfin, ⟨?_, hbij.injOn.mono Set.diff_subset, ?_⟩,
      fun x hx => hS x hx.1⟩⟩
  · rintro y ⟨x, hx, rfl⟩; exact hbij.mapsTo (hW hx)
  · rintro y ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  · rintro x ⟨hx, hxW⟩
    refine ⟨hbij.mapsTo hx, ?_⟩
    rintro ⟨w, hw, hwx⟩
    exact hxW (hbij.injOn (hW hw) hx hwx ▸ hw)
  · rintro y ⟨hy, hy'⟩
    obtain ⟨x, hx, rfl⟩ := hbij.surjOn hy
    exact ⟨x, ⟨hx, fun hxW => hy' ⟨x, hxW, rfl⟩⟩, rfl⟩

/-- Transport equidecomposability along a group homomorphism compatible with the actions. -/
