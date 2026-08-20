/-
# Gauss Bonnet Polygon
Category: Pure Mathematics
Target: Math.gauss_bonnet_polygon
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gauss Bonnet Polygon
Category: Pure Mathematics
Target: Math.gauss_bonnet_polygon
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Metric Set Module Real
open scoped RealInnerProductSpace ENNReal Pointwise

namespace Math

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The cross product of two vectors of `ℝ³`. -/

theorem volume_hemiCone {u : E3} (hu : u ≠ 0) :
    volume (hemiCone u) = ENNReal.ofReal (2 * π / 3) := by
  have hb : MeasurableSet {x : E3 | ‖x‖ < 1} :=
    (isOpen_lt continuous_norm continuous_const).measurableSet
  have h1 : {x : E3 | ‖x‖ < 1} ∩ {x | 0 < ⟪u, x⟫} = hemiCone u := rfl
  have h2 : {x : E3 | ‖x‖ < 1} ∩ {x | 0 < ⟪-u, x⟫} = hemiCone (-u) := rfl
  have hneg : hemiCone (-u) = -(hemiCone u) := by
    ext x; simp [hemiCone, inner_neg_left, inner_neg_right]
  have key := volume_split {x : E3 | ‖x‖ < 1} hb hu
  rw [h1, h2, hneg, Measure.measure_neg, volume_unitBall, ← two_mul] at key
  have h4 : ENNReal.ofReal (4 * π / 3) = 2 * ENNReal.ofReal (2 * π / 3) := by
    rw [show (4:ℝ) * π / 3 = 2 * (2 * π / 3) by ring, ENNReal.ofReal_mul (by norm_num)]
    norm_num
  rw [h4] at key
  exact ((ENNReal.mul_right_inj (by norm_num) (by norm_num)).mp key).symm

/-! ### The area of a planar sector, by polar coordinates -/

/-- Description of the sector `{cos φ > 0} ∩ {cos (φ - θ) > 0}` as an interval of angles. -/
