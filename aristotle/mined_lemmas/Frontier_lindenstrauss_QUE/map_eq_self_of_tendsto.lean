/-
# Lindenstrauss QUE
Category: Frontier — Fields Medal Work
Target: Frontier.lindenstrauss_QUE
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open MeasureTheory Filter Topology TopologicalSpace
open scoped BoundedContinuousFunction

namespace Frontier

section Abstract

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

omit [CompactSpace X] in
/-- A weak-* limit of a sequence of `T`-invariant probability measures is `T`-invariant.

This is the standard "limit measures are geodesic-flow invariant" step in the
quantum-unique-ergodicity argument. -/

theorem map_eq_self_of_tendsto {T : X → X} (hT : Continuous T)
    (mu : ℕ → ProbabilityMeasure X) (nu : ProbabilityMeasure X)
    (hinv : ∀ n, Measure.map T (mu n : Measure X) = (mu n : Measure X))
    (hconv : Tendsto mu atTop (𝓝 nu)) :
    Measure.map T (nu : Measure X) = (nu : Measure X) := by
  have hmeas : Measurable T := hT.measurable
  haveI : IsProbabilityMeasure (Measure.map T (nu : Measure X)) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure (fun f => ?_)
  have key : ∀ mm : ProbabilityMeasure X,
      ∫ x, f x ∂(Measure.map T (mm : Measure X))
        = ∫ x, (f.compContinuous ⟨T, hT⟩) x ∂(mm : Measure X) := by
    intro mm
    rw [integral_map hmeas.aemeasurable f.continuous.aestronglyMeasurable]
    rfl
  have h1 : Tendsto (fun n => ∫ x, (f.compContinuous ⟨T, hT⟩) x ∂(mu n : Measure X)) atTop
      (𝓝 (∫ x, (f.compContinuous ⟨T, hT⟩) x ∂(nu : Measure X))) :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv _
  have h2 : Tendsto (fun n => ∫ x, f x ∂(mu n : Measure X)) atTop
      (𝓝 (∫ x, f x ∂(nu : Measure X))) :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv _
  have h3 : ∀ n, ∫ x, (f.compContinuous ⟨T, hT⟩) x ∂(mu n : Measure X)
      = ∫ x, f x ∂(mu n : Measure X) := by
    intro n
    rw [← key (mu n), hinv n]
  rw [key nu]
  simp only [h3] at h1
  exact tendsto_nhds_unique h1 h2

/-- **Reduction of QUE to measure classification.**

If every weak-* subsequential limit of a sequence of `T`-invariant probability measures is
the given (Haar) measure, then the whole sequence converges weak-* to it. -/
