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


theorem symm [Nonempty X] {A B : Set X} (h : Equidecomp G A B) : Equidecomp G B A := by
  obtain ⟨f, S, hSfin, hbij, hS⟩ := h
  refine ⟨Function.invFunOn f A, S⁻¹, hSfin.inv, hbij.invOn_invFunOn.symm.bijOn ?_ ?_, ?_⟩
  · intro y hy
    exact Function.invFunOn_mem (hbij.surjOn hy)
  · intro x hx
    exact hbij.mapsTo hx
  · intro y hy
    have hx : Function.invFunOn f A y ∈ A := Function.invFunOn_mem (hbij.surjOn hy)
    have hfx : f (Function.invFunOn f A y) = y := Function.invFunOn_eq (hbij.surjOn hy)
    obtain ⟨g, hg, hgx⟩ := hS _ hx
    refine ⟨g⁻¹, by simpa using hg, ?_⟩
    rw [hgx] at hfx
    conv_rhs => rw [← hfx]
    rw [inv_smul_smul]

