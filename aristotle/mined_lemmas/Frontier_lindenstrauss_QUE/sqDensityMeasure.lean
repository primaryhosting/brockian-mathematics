import Mathlib

/-!
# Lindenstrauss QUE
Category: Frontier — Fields Medal Work
Target: Frontier.lindenstrauss_QUE
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open MeasureTheory Filter Topology

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **Weak-\* compactness reduction.**  If every subsequential weak-\* limit of a sequence of
probability measures on a compact metric space equals `vol`, then the whole sequence converges
weak-\* to `vol`. -/

noncomputable def sqDensityMeasure (vol : Measure X) (f : C(X, ℝ)) : Measure X :=
  vol.withDensity (fun x => (Real.toNNReal (f x ^ 2) : ℝ≥0∞))

omit [CompactSpace X] in
