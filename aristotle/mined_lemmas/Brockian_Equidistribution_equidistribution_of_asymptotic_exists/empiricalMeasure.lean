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
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace Brockian.Equidistribution

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]

/-- The empirical measure of the first `N + 1` terms of the sequence `x`: the average of the
Dirac masses at `x 0, …, x N`. -/

noncomputable def empiricalMeasure (x : ℕ → X) (N : ℕ) : Measure X :=
  ((N : ℝ≥0∞) + 1)⁻¹ • ∑ n ∈ Finset.range (N + 1), Measure.dirac (x n)

instance instIsProbabilityMeasureEmpiricalMeasure (x : ℕ → X) (N : ℕ) :
    IsProbabilityMeasure (empiricalMeasure x N) := by
  constructor
  simp only [empiricalMeasure, Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply,
    smul_eq_mul]
  simp [ENNReal.inv_mul_cancel]

/-- Integrating a continuous function against the empirical measure gives the Cesàro average. -/
