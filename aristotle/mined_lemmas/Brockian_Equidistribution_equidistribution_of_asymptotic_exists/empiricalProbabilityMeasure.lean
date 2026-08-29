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

noncomputable def empiricalProbabilityMeasure (x : ℕ → X) (N : ℕ) : ProbabilityMeasure X :=
  ⟨empiricalMeasure x N, inferInstance⟩

/-- **Existence of asymptotic averages implies equidistribution with respect to some probability
measure.**

Let `X` be a compact Hausdorff space with its Borel σ-algebra and let `x : ℕ → X` be a sequence.
If for every continuous real-valued function `f` on `X` the Cesàro averages
`(1/N) * ∑_{n < N} f (x n)` converge to *some* real number, then there is a single Borel
probability measure `μ` on `X` such that these averages converge to `∫ f dμ` for every continuous
`f`; that is, `x` is equidistributed with respect to `μ`.

The measure is produced unconditionally: nothing about the existence of a limiting measure is
assumed, only the existence of the scalar limits. -/
