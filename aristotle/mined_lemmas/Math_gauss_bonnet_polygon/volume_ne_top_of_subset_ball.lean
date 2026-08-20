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

theorem volume_ne_top_of_subset_ball {S : Set E3} (hS : S ⊆ {x : E3 | ‖x‖ < 1}) :
    volume S ≠ ⊤ :=
  ne_top_of_le_ne_top (by rw [volume_unitBall]; exact ENNReal.ofReal_ne_top) (measure_mono hS)

