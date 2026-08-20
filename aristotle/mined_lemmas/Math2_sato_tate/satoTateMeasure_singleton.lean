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

open scoped Real ENNReal NNReal Classical
open MeasureTheory Filter Topology Set

namespace Math2

/-- The Sato–Tate density on `[0, π]`: `θ ↦ (2/π) sin²θ`. -/

lemma satoTateMeasure_singleton (x : ℝ) : satoTateMeasure {x} = 0 := by
  rw [satoTateMeasure, withDensity_apply _ (measurableSet_singleton x)]
  refine setLIntegral_measure_zero _ _ ?_
  simp

/-- The Sato–Tate measure gives no mass to the boundary of an interval. -/
