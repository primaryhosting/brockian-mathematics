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


private theorem cross_dot_self (v w : Fin 3 → ℝ) :
    (v ⨯₃ w) ⬝ᵥ (v ⨯₃ w) = (v ⬝ᵥ v) * (w ⬝ᵥ w) - (v ⬝ᵥ w) ^ 2 := by
  simp [cross_apply, dotProduct, Fin.sum_univ_three]; ring

