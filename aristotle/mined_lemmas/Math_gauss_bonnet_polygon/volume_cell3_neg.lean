/-
Volume of a wedge of the unit ball of `EuclideanSpace ℝ (Fin 3)` in standard position.

This is an auxiliary file for the Gauss-Bonnet (Girard) theorem for spherical triangles.
-/
import RequestProject.Sector

open MeasureTheory Metric Set Real
open scoped ENNReal

namespace Math

/-- Euclidean 3-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The wedge of the unit ball cut out by the half-spaces with inner normals
`(1,0,0)` and `(cos t, sin t, 0)`. -/

theorem volume_cell3_neg (n m p : E3) :
    volume (cell3 (-n) (-m) (-p)) = volume (cell3 n m p) := by
  have hset : cell3 (-n) (-m) (-p) = Neg.neg ⁻¹' (cell3 n m p) := by
    ext x
    simp only [cell3, cell2, cell1, cone1, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage,
      inner_neg_left, inner_neg_right, mem_ball_zero_iff, norm_neg, neg_neg]
    tauto
  rw [hset, Measure.measure_preimage_neg]

end Math

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
Volume of a general wedge of the unit ball of `ℝ³`, obtained from the standard one by a rotation.

This is an auxiliary file for the Gauss-Bonnet (Girard) theorem for spherical triangles.
-/
import RequestProject.Wedge

open MeasureTheory Metric Set Real InnerProductGeometry
open scoped ENNReal RealInnerProductSpace

namespace Math

/-- The wedge of the closed unit ball cut out by the two half-spaces with inner unit normals
`n` and `m`. -/
