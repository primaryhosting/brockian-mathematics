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

theorem isOpen_hemiCone (u : E3) : IsOpen (hemiCone u) := by
  have h1 : IsOpen {x : E3 | ‖x‖ < 1} := isOpen_lt continuous_norm continuous_const
  have h2 : IsOpen {x : E3 | 0 < ⟪u, x⟫} := isOpen_lt continuous_const (by fun_prop)
  exact h1.inter h2

