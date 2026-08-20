import RequestProject.GaussBonnet.WedgeGeneral
import RequestProject.GaussBonnet.Angle
import RequestProject.GaussBonnet.Girard

/-!
# Gauss Bonnet Polygon
Category: Pure Mathematics
Target: Math.gauss_bonnet_polygon
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

**Girard's theorem** (the Gauss–Bonnet theorem for a geodesic triangle on the unit sphere):
the sum of the three interior angles of a spherical triangle exceeds `π` by its area.
-/

open MeasureTheory Real InnerProductGeometry RealInnerProductSpace Metric

namespace Math

/-- The inward normal to the side `BC` of the spherical triangle `ABC`, normalised so that
`⟪A, nrm A B C⟫ = 1`. -/

lemma det_ne_zero (A B C : E3) (hind : LinearIndependent ℝ ![A, B, C]) :
    ⟪A, cross B C⟫ ≠ 0 := by
  intro h
  set M : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun i j => (![A, B, C] j).ofLp i with hM
  have hdet : M.det = ⟪A, cross B C⟫ := by
    rw [Matrix.det_fin_three]
    simp only [hM, Matrix.of_apply, inner_eq_three, cross_apply, crossProduct]
    simp only [LinearMap.mk₂_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    ring
  obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := M)).2 (by rw [hdet, h])
  rw [Fintype.linearIndependent_iff] at hind
  have hsum : ∑ j, v j • (![A, B, C] j) = 0 := by
    ext i
    simpa [Matrix.mulVec, dotProduct, hM, mul_comm] using congrFun hv i
  exact hv0 (funext fun i => hind v hsum i)

/-- The normal `nrm A B C` is orthogonal to `B` and `C` and normalised at `A`. -/
