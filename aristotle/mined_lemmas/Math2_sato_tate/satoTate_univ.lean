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
open scoped ENNReal NNReal BoundedContinuousFunction

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

namespace Math2

open MeasureTheory Filter Topology Set

/-! ## The Sato–Tate measure -/

/-- The Sato–Tate measure on `ℝ`: the probability measure supported on `[0, π]` with
density `(2/π) · sin²θ` with respect to Lebesgue measure. -/

theorem satoTate_univ : satoTateMeasure Set.univ = 1 := by
  rw [satoTate_apply _ MeasurableSet.univ, Set.univ_inter,
    integral_satoTate_density Real.pi_pos.le]
  have := Real.pi_pos
  simp [Real.sin_pi, Real.sin_zero]

instance : IsProbabilityMeasure satoTateMeasure := ⟨satoTate_univ⟩

/-- The Sato–Tate measure as a bundled probability measure. -/
