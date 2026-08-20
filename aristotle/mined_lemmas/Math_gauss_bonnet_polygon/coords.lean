import RequestProject.Sector

open MeasureTheory Metric Set Real InnerProductGeometry
open scoped ENNReal RealInnerProductSpace

namespace Math

/-- Euclidean three-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The volume of the standard solid wedge of dihedral angle `psi` inside the unit ball:
the axis of the wedge is the first coordinate axis, and the wedge is described in the plane
of the last two coordinates as the cone spanned by `(1,0)` and `(cos psi, sin psi)`. -/

theorem coords (u v w : E3) (hind : LinearIndependent ℝ ![u, v, w]) :
    ∃ f g h : E3 →ₗ[ℝ] ℝ,
      (∀ x : E3, (f x) • u + (g x) • v + (h x) • w = x) ∧
      (∀ a b c : ℝ, f (a • u + b • v + c • w) = a) ∧
      (∀ a b c : ℝ, g (a • u + b • v + c • w) = b) ∧
      (∀ a b c : ℝ, h (a • u + b • v + c • w) = c) := by
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ E3 := by simp
  set B : Module.Basis (Fin 3) ℝ E3 := basisOfLinearIndependentOfCardEqFinrank hind hcard with hBdef
  have hB : ⇑B = ![u, v, w] := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have h0 : B 0 = u := by rw [hB]; rfl
  have h1 : B 1 = v := by rw [hB]; rfl
  have h2 : B 2 = w := by rw [hB]; rfl
  refine ⟨B.coord 0, B.coord 1, B.coord 2, ?_, ?_, ?_, ?_⟩
  · intro x
    have := B.sum_repr x
    rw [Fin.sum_univ_three, h0, h1, h2] at this
    simpa [Module.Basis.coord_apply] using this
  all_goals
    intro a b c
    simp [Module.Basis.coord_apply, ← h0, ← h1, ← h2, Module.Basis.repr_self]

