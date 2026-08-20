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

lemma det_cyclic (A B C : E3) : ⟪B, cross C A⟫ = ⟪A, cross B C⟫ := by
  simp only [inner_eq_three, cross_apply, crossProduct]
  simp only [LinearMap.mk₂_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

