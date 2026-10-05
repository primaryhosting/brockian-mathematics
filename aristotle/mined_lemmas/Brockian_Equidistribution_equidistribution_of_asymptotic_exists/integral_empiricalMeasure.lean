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

lemma integral_empiricalMeasure (x : ℕ → X) (N : ℕ) (f : C(X, ℝ)) :
    ∫ y, f y ∂(empiricalMeasure x N) =
      ((N : ℝ) + 1)⁻¹ * ∑ n ∈ Finset.range (N + 1), f (x n) := by
  rw [empiricalMeasure, integral_smul_measure,
    integral_finset_sum_measure (fun i _ => integrable_dirac (by simp [enorm_eq_nnnorm]))]
  simp [ENNReal.toReal_inv, ENNReal.toReal_add]

/-- The empirical measures, viewed as elements of the space of probability measures. -/
