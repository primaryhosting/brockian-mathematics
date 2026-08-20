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

theorem measure_union_null_right {α : Type*} [MeasurableSpace α] {μ : Measure α} {s t : Set α}
    (h : μ t = 0) : μ (s ∪ t) = μ s :=
  le_antisymm (le_trans (measure_union_le s t) (by rw [h, add_zero]))
    (measure_mono Set.subset_union_left)

