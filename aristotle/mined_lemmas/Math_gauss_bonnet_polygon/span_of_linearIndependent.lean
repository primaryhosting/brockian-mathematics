import RequestProject.Wedge

/-!
# Girard's relation for a solid cone over a spherical triangle

Given three vectors `u v w` in `ℝ³` in general position, the region
`Reg u v w`, the part of the unit ball where the three linear forms `⟪u,·⟫`, `⟪v,·⟫`, `⟪w,·⟫`
are nonnegative, has volume `((π - angle v w) + (π - angle u w) + (π - angle u v) - π)/3`.

This is Girard's theorem in disguise: the three quantities `π - angle · ·` are the dihedral
angles of the cone, and three times the volume of the cone is the area of the spherical
triangle it cuts out on the unit sphere.
-/

open MeasureTheory Metric Set Real InnerProductGeometry

namespace Math

/-- The closed half-space with inner normal `n`. -/

theorem span_of_linearIndependent {a b c : E3} (hli : LinearIndependent ℝ ![a, b, c]) (x : E3) :
    ∃ p q r : ℝ, x = p • a + q • b + r • c := by
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ E3 := by simp
  let B := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hB : ⇑B = ![a, b, c] := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  refine ⟨B.repr x 0, B.repr x 1, B.repr x 2, ?_⟩
  have hsum := B.sum_repr x
  rw [Fin.sum_univ_three, hB] at hsum
  simpa using hsum.symm

