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

theorem sphArea_eq_toSphere (S : Set (sphere (0 : E3) 1)) (hS : MeasurableSet S) :
    sphArea (Subtype.val '' S) = ((volume : Measure E3).toSphere S).toReal := by
  rw [Measure.toSphere_apply' _ hS, ENNReal.toReal_mul, sphArea]
  norm_num

/-! ### Basic facts about the cross product -/

