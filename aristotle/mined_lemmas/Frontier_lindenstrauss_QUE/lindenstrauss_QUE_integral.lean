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
open scoped NNReal ENNReal

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A *quantum limit* of a sequence of probability measures `mu` is a weak-* limit of some
subsequence of `mu`.  In the arithmetic setting, `mu n` is the microlocal lift of the `n`-th Hecke
eigenform and its quantum limits are the measures classified by Lindenstrauss's measure rigidity
theorem. -/

theorem lindenstrauss_QUE_integral (vol : ProbabilityMeasure X) (mu : ℕ → ProbabilityMeasure X)
    (hrigid : ∀ nu : ProbabilityMeasure X, IsQuantumLimit mu nu → nu = vol)
    (f : BoundedContinuousFunction X ℝ) :
    Tendsto (fun n => ∫ x, f x ∂(mu n : Measure X)) atTop (𝓝 (∫ x, f x ∂(vol : Measure X))) :=
  (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (lindenstrauss_QUE vol mu hrigid)) f

omit [CompactSpace X] in
/-- Sanity check (base case): the only quantum limit of a constant sequence of probability
measures is that measure itself, so the hypothesis of `Frontier.lindenstrauss_QUE` is satisfiable
and the theorem indeed yields quantum unique ergodicity in that degenerate case. -/
