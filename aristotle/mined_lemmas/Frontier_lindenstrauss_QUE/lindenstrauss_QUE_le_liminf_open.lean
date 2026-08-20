/-
# Lindenstrauss QUE
Category: Frontier — Fields Medal Work
Target: Frontier.lindenstrauss_QUE
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lindenstrauss QUE
Category: Frontier — Fields Medal Work
Target: Frontier.lindenstrauss_QUE
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Filter Topology

namespace Frontier

section QUE

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **Sequential compactness of the space of probability measures.**

On a compact metric space `X`, the space of Borel probability measures with the topology of
weak-* convergence is compact and metrizable, hence sequentially compact: every sequence of
probability measures has a weak-* convergent subsequence.

This is the compactness half of the standard quantum-unique-ergodicity argument: the microlocal
lifts of a sequence of eigenfunctions always have weak-* limit points ("quantum limits"). -/

theorem lindenstrauss_QUE_le_liminf_open (vol : ProbabilityMeasure X)
    (mu : ℕ → ProbabilityMeasure X)
    (h_quantum_limits : ∀ ns : ℕ → ℕ, StrictMono ns → ∀ nu : ProbabilityMeasure X,
      Tendsto (fun n => mu (ns n)) atTop (𝓝 nu) → nu = vol)
    {U : Set X} (hU : IsOpen U) :
    (vol : Measure X) U ≤ liminf (fun n => (mu n : Measure X) U) atTop :=
  ProbabilityMeasure.le_liminf_measure_open_of_tendsto
    (lindenstrauss_QUE vol mu h_quantum_limits).1 hU

end QUE

end Frontier

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

