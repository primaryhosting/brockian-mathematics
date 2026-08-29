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

theorem isQuantumLimit_const_iff (vol nu : ProbabilityMeasure X) :
    IsQuantumLimit (fun _ : ℕ => vol) nu ↔ nu = vol := by
  constructor
  · rintro ⟨phi, -, hconv⟩
    exact tendsto_nhds_unique hconv tendsto_const_nhds
  · rintro rfl
    exact ⟨id, strictMono_id, tendsto_const_nhds⟩

/-- Base case of `Frontier.lindenstrauss_QUE`: a constant sequence converges to its value. -/
