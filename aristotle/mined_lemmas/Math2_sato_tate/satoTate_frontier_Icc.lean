/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal NNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

open MeasureTheory Filter Topology Set

/-- The Sato–Tate density on `[0, π]`: `θ ↦ (2/π) sin²θ`. -/

lemma satoTate_frontier_Icc (α β : ℝ) : satoTateMeasure (frontier (Icc α β)) = 0 := by
  have habs : satoTateMeasure ≪ volume := by
    refine (withDensity_absolutelyContinuous _ _).trans ?_
    exact Measure.absolutelyContinuous_of_le Measure.restrict_le_self
  refine habs ?_
  refine measure_mono_null (frontier_Icc_subset α β) ?_
  exact measure_union_null (measure_singleton α) (measure_singleton β)

