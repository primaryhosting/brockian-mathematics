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

lemma measurableSet_std (f : ℝ) : MeasurableSet
    {y : E3 | ‖y‖ ≤ 1 ∧ 0 ≤ y.ofLp 0 ∧ 0 ≤ cos f * y.ofLp 0 + sin f * y.ofLp 1} := by
  have c0 : Continuous fun y : E3 => y.ofLp 0 := by fun_prop
  have h : {y : E3 | ‖y‖ ≤ 1 ∧ 0 ≤ y.ofLp 0 ∧ 0 ≤ cos f * y.ofLp 0 + sin f * y.ofLp 1}
      = {y : E3 | ‖y‖ ≤ 1} ∩ ({y : E3 | 0 ≤ y.ofLp 0} ∩
        {y : E3 | 0 ≤ cos f * y.ofLp 0 + sin f * y.ofLp 1}) := by
    ext y; simp
  rw [h]
  exact ((isClosed_le continuous_norm continuous_const).measurableSet).inter
    (((isClosed_le continuous_const c0).measurableSet).inter
      ((isClosed_le continuous_const (by fun_prop)).measurableSet))

/-- The volume of a solid wedge, for unit vectors. -/
